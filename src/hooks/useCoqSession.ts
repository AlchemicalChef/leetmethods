'use client';

import { useEffect, useState, useCallback, useRef } from 'react';
import { getCoqService, softResetCoqService, setInitializing } from '@/lib/coq';
import type { CoqService, CoqGoal } from '@/lib/coq';
import { useCoqStore } from '@/store/coqStore';
import { formatError } from '@/lib/format-error';

export interface UseCoqSessionOptions {
  /** Coq prelude to prepend before user code. May change over time (e.g. per tutorial step). */
  prelude: string;
  /**
   * Optional override for goal updates. When provided, the hook calls this
   * instead of (in addition to) the default `setGoals` from the store.
   * The default store `setGoals` is always called; use this for side-effects
   * like detecting proof completion.
   */
  onGoalsUpdate?: (goals: CoqGoal[]) => void;
  /**
   * Called before every execute/executeAll/executeToPosition action.
   * Use this to set proof state to 'in_progress', etc.
   */
  onBeforeExecute?: () => void;
  /**
   * Called after a successful reset. The hook clears executedUpTo internally;
   * use this callback for component-specific reset side-effects
   * (e.g. resetting code, submission result, step completion).
   */
  onAfterReset?: () => void;
}

export interface UseCoqSessionReturn {
  serviceRef: React.RefObject<CoqService | null>;
  coqLoading: boolean;
  coqInitError: string | null;
  executedUpTo: number;
  handleExecuteNext: () => Promise<void>;
  handleExecutePrev: () => Promise<void>;
  handleExecuteAll: () => Promise<void>;
  handleExecuteToPosition: (charOffset: number) => Promise<void>;
  handleReset: () => Promise<void>;
  /** Manually trigger Coq service initialization (e.g. on problem change). */
  initializeCoqService: () => Promise<void>;
}

/**
 * Encapsulates Coq service lifecycle, execution handlers, and position tracking.
 *
 * Both ProblemSolver and TutorialPage need identical Coq init, execution wiring,
 * and cleanup logic. This hook extracts that shared concern while remaining
 * composable via callbacks for component-specific behavior (proof state transitions,
 * step completion detection, code reset).
 *
 * The hook does NOT own the editor code state -- callers manage their own code
 * and pass a ref via `codeRef` so the hook always reads the latest value
 * without re-rendering on every keystroke.
 */
export function useCoqSession(
  codeRef: React.RefObject<string>,
  options: UseCoqSessionOptions,
): UseCoqSessionReturn {
  const { setGoals, setStatus, addMessage } = useCoqStore();

  const [coqLoading, setCoqLoading] = useState(false);
  const [coqInitError, setCoqInitError] = useState<string | null>(null);
  const [executedUpTo, setExecutedUpTo] = useState(0);

  const serviceRef = useRef<CoqService | null>(null);
  const preludeRef = useRef(options.prelude);

  // Keep preludeRef in sync so the onPositionChange closure always reads the
  // latest prelude without needing to re-create the callback set.
  useEffect(() => {
    preludeRef.current = options.prelude;
  }, [options.prelude]);

  // Stabilize option callbacks via refs to avoid re-creating the init callback
  // every time the consumer re-renders with a new closure.
  const onGoalsUpdateRef = useRef(options.onGoalsUpdate);
  const onBeforeExecuteRef = useRef(options.onBeforeExecute);
  const onAfterResetRef = useRef(options.onAfterReset);

  useEffect(() => { onGoalsUpdateRef.current = options.onGoalsUpdate; }, [options.onGoalsUpdate]);
  useEffect(() => { onBeforeExecuteRef.current = options.onBeforeExecute; }, [options.onBeforeExecute]);
  useEffect(() => { onAfterResetRef.current = options.onAfterReset; }, [options.onAfterReset]);

  // ── Initialization ──────────────────────────────────────────────────

  const initializeCoqService = useCallback(async () => {
    setCoqLoading(true);
    setCoqInitError(null);
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
          // Subtract prelude length (prelude + '\n\n') to get editor-relative offset.
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
  // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [setStatus, setGoals, addMessage]);

  // ── Execution Handlers ──────────────────────────────────────────────

  const handleExecuteNext = useCallback(async () => {
    if (!serviceRef.current) return;
    try {
      const currentCode = codeRef.current;
      serviceRef.current.setCode(preludeRef.current + '\n\n' + currentCode);
      onBeforeExecuteRef.current?.();
      await serviceRef.current.executeNext();
    } catch (error) {
      console.error('[useCoqSession] executeNext failed:', error);
      addMessage('error', formatError(error, 'Execution failed'));
    }
  }, [codeRef, addMessage]);

  const handleExecutePrev = useCallback(async () => {
    if (!serviceRef.current) return;
    try {
      await serviceRef.current.executePrev();
    } catch (error) {
      console.error('[useCoqSession] executePrev failed:', error);
      addMessage('error', formatError(error, 'Undo failed'));
    }
  }, [addMessage]);

  const handleExecuteToPosition = useCallback(async (charOffset: number) => {
    if (!serviceRef.current) return;
    try {
      const currentCode = codeRef.current;
      serviceRef.current.setCode(preludeRef.current + '\n\n' + currentCode);
      onBeforeExecuteRef.current?.();
      const preludeLen = preludeRef.current.length + 2;
      await serviceRef.current.executeToPosition(charOffset + preludeLen);
    } catch (error) {
      console.error('[useCoqSession] executeToPosition failed:', error);
      addMessage('error', formatError(error, 'Execution failed'));
    }
  }, [codeRef, addMessage]);

  const handleExecuteAll = useCallback(async () => {
    if (!serviceRef.current) return;
    try {
      const currentCode = codeRef.current;
      serviceRef.current.setCode(preludeRef.current + '\n\n' + currentCode);
      onBeforeExecuteRef.current?.();
      await serviceRef.current.executeAll();
    } catch (error) {
      console.error('[useCoqSession] executeAll failed:', error);
      addMessage('error', formatError(error, 'Execution failed'));
    }
  }, [codeRef, addMessage]);

  const handleReset = useCallback(async () => {
    if (!serviceRef.current) return;
    try {
      await serviceRef.current.reset();
      setExecutedUpTo(0);
      onAfterResetRef.current?.();
    } catch (error) {
      console.error('[useCoqSession] reset failed:', error);
      addMessage('error', formatError(error, 'Reset failed'));
    }
  }, [addMessage]);

  // ── Cleanup ─────────────────────────────────────────────────────────

  useEffect(() => {
    return () => {
      softResetCoqService();
    };
  }, []);

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
  };
}
