/**
 * @module useCoqSession
 *
 * Shared React hook that encapsulates the full Coq service lifecycle:
 * initialization, code execution (step-by-step, to-position, and run-all),
 * undo, reset, and cleanup.
 *
 * Both `ProblemSolver` and `TutorialPage` need identical Coq integration
 * logic, so this hook extracts the shared concern while remaining composable.
 * Component-specific behavior (proof state transitions, step completion
 * detection, code resets) is injected via callback options.
 *
 * Architecture:
 * ```
 * ProblemSolver / TutorialPage
 *   -> useCoqSession(codeRef, options)
 *     -> CoqService singleton (src/lib/coq/CoqService.ts)
 *       -> hidden iframe (public/coq-worker.html)
 *         -> jsCoq 0.17.1 via postMessage IPC
 * ```
 *
 * Key design decisions:
 *
 * 1. **codeRef pattern**: The hook does NOT own the editor code state.
 *    Callers pass a React ref to their code string so the hook always reads
 *    the latest value without triggering re-renders on every keystroke.
 *    This decouples the Coq execution layer from the editor state.
 *
 * 2. **Prelude offset math**: User code is prepended with a Coq prelude
 *    (imports, helper lemmas). The hook adds this prelude before sending
 *    code to jsCoq and subtracts the prelude length from position callbacks
 *    so the editor sees character offsets relative to the user's code only.
 *    The +2 accounts for the "\n\n" separator between prelude and user code.
 *
 * 3. **Ref-stabilized callbacks**: Options like `onGoalsUpdate`, `onBeforeExecute`,
 *    and `onAfterReset` are stored in refs and synced via effects. This prevents
 *    the initialization callback from being re-created every time the consumer
 *    re-renders with a new closure, which would cause unnecessary Coq re-inits.
 *
 * 4. **Singleton lifecycle**: `getCoqService()` returns a singleton; the iframe
 *    persists across navigations. On unmount, `softResetCoqService()` resets
 *    the Coq state without destroying the iframe (expensive re-init). The
 *    `setInitializing()` flag prevents React Strict Mode double-mount from
 *    racing to destroy the singleton during initialization.
 *
 * 5. **Error handling**: All execution handlers catch errors, log them to
 *    the console, and surface user-friendly messages via `addMessage('error', ...)`.
 */

'use client';

import { useEffect, useLayoutEffect, useState, useCallback, useRef } from 'react';
import { getCoqService, softResetCoqService, setInitializing } from '@/lib/coq';
import type { CoqService, CoqGoal } from '@/lib/coq';
import { useCoqStore } from '@/store/coqStore';
import { formatError } from '@/lib/format-error';
import { computeErrorDiagnostic } from '@/lib/coq/coq-diagnostics';
import type { CoqDiagnostic } from '@/lib/coq/coq-diagnostics';

/* ─── Hook Options Interface ────────────────────────────────────────────── */

export interface UseCoqSessionOptions {
  /**
   * Coq prelude to prepend before user code. Typically contains `Require Import`
   * statements and helper lemma definitions. May change over time (e.g., each
   * tutorial step can have its own prelude).
   */
  prelude: string;

  /**
   * Optional callback invoked whenever jsCoq reports updated goals.
   * The default store `setGoals` is always called; this callback is for
   * additional side-effects like detecting proof completion or updating
   * tutorial step state.
   *
   * @param goals - The current proof goals returned by jsCoq.
   */
  onGoalsUpdate?: (goals: CoqGoal[]) => void;

  /**
   * Called before every execute action (executeNext, executeAll, executeToPosition).
   * Use this to transition proof state to 'in_progress', clear stale 'completed'
   * state from previous submissions, or perform pre-execution bookkeeping.
   */
  onBeforeExecute?: () => void;

  /**
   * Called after a successful reset. The hook clears `executedUpTo` internally;
   * use this callback for component-specific reset side-effects such as
   * resetting code to the template, clearing submission results, or
   * resetting tutorial step completion flags.
   */
  onAfterReset?: () => void;
}

/* ─── Hook Return Interface ─────────────────────────────────────────────── */

export interface UseCoqSessionReturn {
  /** Ref to the CoqService instance (null before initialization). */
  serviceRef: React.RefObject<CoqService | null>;

  /** True while the Coq service is loading/initializing. */
  coqLoading: boolean;

  /** Error message if Coq initialization failed, null otherwise. */
  coqInitError: string | null;

  /**
   * Character offset in the user's code (NOT including prelude) up to which
   * Coq has successfully executed. Used by the editor to render the
   * "executed region" highlight.
   */
  executedUpTo: number;

  /** Execute the next Coq sentence after the current position. */
  handleExecuteNext: () => Promise<void>;

  /** Undo the last executed Coq sentence (step backward). */
  handleExecutePrev: () => Promise<void>;

  /** Execute all Coq sentences in the code from the beginning. */
  handleExecuteAll: () => Promise<void>;

  /**
   * Execute Coq sentences up to a specific character offset in the user's code.
   * The offset is automatically adjusted by the prelude length before being
   * sent to CoqService.
   *
   * @param charOffset - Character offset in the user's code (0-based).
   */
  handleExecuteToPosition: (charOffset: number) => Promise<void>;

  /** Reset the Coq session, clearing all executed state. */
  handleReset: () => Promise<void>;

  /**
   * Manually trigger Coq service initialization. Called on mount and can be
   * called again when switching problems/tutorial steps that need a fresh
   * Coq session.
   */
  initializeCoqService: () => Promise<void>;

  /** Diagnostic for the current error (null when no error). */
  errorDiagnostic: CoqDiagnostic | null;

  /** Clears the current error diagnostic (e.g., when user edits code). */
  clearErrorDiagnostic: () => void;
}

/* ─── Hook Implementation ───────────────────────────────────────────────── */

/**
 * Core Coq session management hook shared by ProblemSolver and TutorialPage.
 *
 * @param codeRef - React ref to the current editor code string. The hook reads
 *   this ref (not a state value) to avoid re-renders on every keystroke.
 * @param options - Configuration for prelude, and lifecycle callbacks.
 * @returns Object containing service ref, loading/error state, position tracking,
 *   and bound execution handlers.
 */
export function useCoqSession(
  codeRef: React.RefObject<string>,
  options: UseCoqSessionOptions,
): UseCoqSessionReturn {
  const { setGoals, setStatus, addMessage } = useCoqStore();

  const [coqLoading, setCoqLoading] = useState(false);
  const [coqInitError, setCoqInitError] = useState<string | null>(null);
  const [executedUpTo, setExecutedUpTo] = useState(0);
  const [errorDiagnostic, setErrorDiagnostic] = useState<CoqDiagnostic | null>(null);

  const clearErrorDiagnostic = useCallback(() => setErrorDiagnostic(null), []);

  const serviceRef = useRef<CoqService | null>(null);
  const preludeRef = useRef(options.prelude);

  /**
   * Keep preludeRef in sync with the latest prelude value. This ensures
   * the onPositionChange closure (created once during init) always reads
   * the current prelude length for offset math, even if the prelude changes
   * (e.g., when navigating between tutorial steps).
   */
  useEffect(() => {
    preludeRef.current = options.prelude;
  }, [options.prelude]);

  /* ── Ref-stabilized callbacks ───────────────────────────────────────────
   *
   * Store option callbacks in refs so the init callback (memoized with
   * useCallback) doesn't need them in its dependency array. Without this,
   * every re-render of the consumer that creates new closure instances for
   * these callbacks would invalidate the init callback and potentially
   * trigger re-initialization.
   * ──────────────────────────────────────────────────────────────────── */
  const onGoalsUpdateRef = useRef(options.onGoalsUpdate);
  const onBeforeExecuteRef = useRef(options.onBeforeExecute);
  const onAfterResetRef = useRef(options.onAfterReset);

  useLayoutEffect(() => { onGoalsUpdateRef.current = options.onGoalsUpdate; }, [options.onGoalsUpdate]);
  useLayoutEffect(() => { onBeforeExecuteRef.current = options.onBeforeExecute; }, [options.onBeforeExecute]);
  useLayoutEffect(() => { onAfterResetRef.current = options.onAfterReset; }, [options.onAfterReset]);

  /* ── Initialization ───────────────────────────────────────────────────── */

  const initializeCoqService = useCallback(async () => {
    setCoqLoading(true);
    setCoqInitError(null);

    /**
     * Set the global initializing flag to prevent React Strict Mode's
     * double-mount from destroying the singleton mid-initialization.
     * The flag is cleared in both success and error paths below.
     */
    setInitializing(true);

    try {
      const service = getCoqService({
        onStatusChange: setStatus,
        onGoalsUpdate: (goals) => {
          setGoals(goals);
          onGoalsUpdateRef.current?.(goals);
        },
        onMessage: (msg) => addMessage(msg.type, msg.content),
        onPositionChange: (charOffset) => {
          /**
           * Convert the absolute character offset (which includes the prelude)
           * into an editor-relative offset by subtracting the prelude length.
           * The +2 accounts for the "\n\n" separator inserted between the
           * prelude and user code. Clamped to 0 to avoid negative offsets
           * when Coq reports a position within the prelude itself.
           */
          const preludeLen = preludeRef.current.length + 2;
          setExecutedUpTo(Math.max(0, charOffset - preludeLen));
        },
        onReady: () => {
          setStatus('ready');
          setCoqLoading(false);
          setInitializing(false);
        },
        onError: (error) => {
          setCoqInitError(error);
          setCoqLoading(false);
          setInitializing(false);
        },
      });

      await service.initialize();
      serviceRef.current = service;
      setCoqLoading(false);
      setInitializing(false);
    } catch (error) {
      const errorMsg = formatError(error, 'Failed to initialize Coq');
      setCoqInitError(errorMsg);
      setCoqLoading(false);
      setInitializing(false);
    }
  /**
   * Dependency note: setStatus, setGoals, and addMessage are stable Zustand
   * selectors that don't change between renders. The ref-stabilized callbacks
   * (onGoalsUpdateRef, etc.) are intentionally excluded because they are
   * accessed via refs, not closure captures.
   */
  // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [setStatus, setGoals, addMessage]);

  /* ── Execution Handlers ───────────────────────────────────────────────── */

  /**
   * Execute the next Coq sentence. Sends the full code (prelude + user code)
   * to CoqService, which tracks its internal position and advances one sentence.
   */
  const handleExecuteNext = useCallback(async () => {
    if (!serviceRef.current) return;
    setErrorDiagnostic(null);
    try {
      const currentCode = codeRef.current;
      const prelude = preludeRef.current;
      const fullCode = prelude + '\n\n' + currentCode;
      serviceRef.current.setCode(fullCode);
      onBeforeExecuteRef.current?.();
      await serviceRef.current.executeNext();
    } catch (error) {
      console.error('[useCoqSession] executeNext failed:', error);
      const errMsg = formatError(error, 'Execution failed');
      addMessage('error', errMsg);
      if (serviceRef.current) {
        const prelude = preludeRef.current;
        const fullCode = prelude + '\n\n' + codeRef.current;
        const diag = computeErrorDiagnostic(fullCode, serviceRef.current.getExecutedCount(), prelude.length, errMsg);
        if (diag) setErrorDiagnostic(diag);
      }
    }
  }, [codeRef, addMessage]);

  /**
   * Undo the last executed sentence (step backward). Does not need to
   * re-send the full code since CoqService tracks its execution state.
   */
  const handleExecutePrev = useCallback(async () => {
    if (!serviceRef.current) return;
    try {
      await serviceRef.current.executePrev();
    } catch (error) {
      console.error('[useCoqSession] executePrev failed:', error);
      addMessage('error', formatError(error, 'Undo failed'));
    }
  }, [addMessage]);

  /**
   * Execute sentences up to a specific character offset in the user's code.
   * The offset is translated to an absolute position by adding the prelude
   * length, since CoqService operates on the full (prelude + code) document.
   */
  const handleExecuteToPosition = useCallback(async (charOffset: number) => {
    if (!serviceRef.current) return;
    setErrorDiagnostic(null);
    try {
      const currentCode = codeRef.current;
      serviceRef.current.setCode(preludeRef.current + '\n\n' + currentCode);
      onBeforeExecuteRef.current?.();
      const preludeLen = preludeRef.current.length + 2;
      await serviceRef.current.executeToPosition(charOffset + preludeLen);
    } catch (error) {
      console.error('[useCoqSession] executeToPosition failed:', error);
      const errMsg = formatError(error, 'Execution failed');
      addMessage('error', errMsg);
      if (serviceRef.current) {
        const prelude = preludeRef.current;
        const fullCode = prelude + '\n\n' + codeRef.current;
        const diag = computeErrorDiagnostic(fullCode, serviceRef.current.getExecutedCount(), prelude.length, errMsg);
        if (diag) setErrorDiagnostic(diag);
      }
    }
  }, [codeRef, addMessage]);

  /**
   * Execute all sentences in the document from the beginning to the end.
   * Used by the "Run All" button and the verification/submission flow.
   */
  const handleExecuteAll = useCallback(async () => {
    if (!serviceRef.current) return;
    setErrorDiagnostic(null);
    try {
      const currentCode = codeRef.current;
      const prelude = preludeRef.current;
      const fullCode = prelude + '\n\n' + currentCode;
      serviceRef.current.setCode(fullCode);
      onBeforeExecuteRef.current?.();
      const result = await serviceRef.current.executeAll();
      if (result.error) {
        const diag = computeErrorDiagnostic(fullCode, serviceRef.current.getExecutedCount(), prelude.length, result.error);
        if (diag) setErrorDiagnostic(diag);
      }
    } catch (error) {
      console.error('[useCoqSession] executeAll failed:', error);
      const errMsg = formatError(error, 'Execution failed');
      addMessage('error', errMsg);
      if (serviceRef.current) {
        const prelude = preludeRef.current;
        const fullCode = prelude + '\n\n' + codeRef.current;
        const diag = computeErrorDiagnostic(fullCode, serviceRef.current.getExecutedCount(), prelude.length, errMsg);
        if (diag) setErrorDiagnostic(diag);
      }
    }
  }, [codeRef, addMessage]);

  /**
   * Reset the Coq session state. Clears the local executedUpTo counter
   * and invokes the caller's onAfterReset callback for component-specific
   * cleanup (e.g., resetting the editor to the problem template).
   */
  const handleReset = useCallback(async () => {
    if (!serviceRef.current) return;
    try {
      await serviceRef.current.reset();
      setExecutedUpTo(0);
      setErrorDiagnostic(null);
      onAfterResetRef.current?.();
    } catch (error) {
      console.error('[useCoqSession] reset failed:', error);
      addMessage('error', formatError(error, 'Reset failed'));
    }
  }, [addMessage]);

  /* ── Cleanup on Unmount ───────────────────────────────────────────────── */

  useEffect(() => {
    return () => {
      /**
       * On unmount, perform a soft reset of the CoqService singleton. This
       * clears the Coq state machine (goals, executed sentences) without
       * destroying the iframe itself. Destroying and re-creating the iframe
       * is expensive (~2-3s), so we preserve it for the next page that needs
       * Coq. Use `resetCoqService()` (not soft) only for full teardown.
       */
      softResetCoqService();
    };
  }, []);

  /* ── Return Value ─────────────────────────────────────────────────────── */

  return {
    serviceRef,
    coqLoading,
    coqInitError,
    executedUpTo,
    handleExecuteNext,
    handleExecutePrev,
    handleExecuteAll,
    handleExecuteToPosition,
    handleReset,
    initializeCoqService,
    errorDiagnostic,
    clearErrorDiagnostic,
  };
}
