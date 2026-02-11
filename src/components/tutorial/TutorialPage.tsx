/**
 * @module TutorialPage
 *
 * Reusable step-by-step interactive tutorial component that drives all
 * guided proof tutorials in the app (e.g., Basics, Logic, Polymorphism).
 *
 * This is one of the most complex components in the app, combining:
 *   - Multi-step navigation with persistent progress (localStorage)
 *   - The shared Coq session lifecycle (useCoqSession hook)
 *   - A split-panel layout with explanation on the left and editor/goals on the right
 *   - Step completion detection via Coq goal state monitoring
 *   - Hint system with show/hide toggle
 *
 * Architecture:
 *   The component receives an array of `TutorialStep` objects that define
 *   each step's explanation, exercise (prelude + template), hint, and success
 *   message. It uses the `useCoqSession` hook to manage the jsCoq iframe
 *   lifecycle, and the `coqStore` for real-time Coq status/goals/messages.
 *
 *   Step progress (which step the user is on) is persisted to localStorage
 *   using a configurable `storageKey` so each tutorial remembers its position
 *   independently.
 *
 * Key design decisions:
 *   - **Completion detection (H4 fix)**: A step is marked complete only when
 *     goals are empty AND the proof was started AND Coq is in 'ready' state.
 *     This three-way check prevents false positives from intermediate states
 *     (e.g., goals being temporarily empty during a reset or mid-execution).
 *   - **Code ref pattern**: The `codeRef` keeps a ref to the latest editor
 *     content so the useCoqSession hook can always read the current code
 *     without needing code in its dependency array (which would cause
 *     excessive re-initialization).
 *   - **eslint-disable comments**: Several are necessary because the effect
 *     dependencies are intentionally incomplete -- e.g., the mount-only
 *     effects must run exactly once, and the useCallback closures capture
 *     values through refs or specific dep tracking.
 *   - **Dynamic routing**: This component is used by `src/app/tutorial/[slug]/page.tsx`
 *     which loads the appropriate step definitions from the tutorial registry.
 *
 * @see useCoqSession - Shared Coq lifecycle hook
 * @see TutorialStep - Step data type definition
 * @see FormattedDescription - Markdown-like text formatter for explanations
 */
'use client';

import { useEffect, useState, useCallback, useRef } from 'react';
import { useHydrated } from '@/hooks/useHydrated';
import { ArrowLeft, ArrowRight, CheckCircle2, Lightbulb, Loader2 } from 'lucide-react';
import { Button } from '@/components/ui/button';
import { Card } from '@/components/ui/card';
import { CoqEditor, GoalsPanel, EditorToolbar, CoqStatusBar } from '@/components/editor';
import { useCoqStore } from '@/store/coqStore';
import { useCoqSession } from '@/hooks/useCoqSession';
import type { CoqGoal } from '@/lib/coq';
import type { TutorialStep } from '@/lib/tutorial/tutorial-steps';
import { FormattedDescription } from '@/lib/format-text';
import Link from 'next/link';

/* ========================================================================
 * Component Props
 * ======================================================================== */

/**
 * Props for the TutorialPage component.
 *
 * @property steps - Ordered array of tutorial step definitions, each containing
 *   an explanation, exercise (prelude + template), hint, and success message.
 * @property title - Display title for the tutorial (shown in the header).
 * @property storageKey - Unique localStorage key for persisting the current step
 *   index across page reloads. Each tutorial should use a distinct key.
 * @property completionLink - Link displayed after the user finishes the last
 *   step, typically pointing back to the tutorial index or the next tutorial.
 */
interface TutorialPageProps {
  steps: TutorialStep[];
  title: string;
  storageKey: string;
  completionLink: { href: string; label: string };
}

/* ========================================================================
 * localStorage Helpers
 * ======================================================================== */

/**
 * Retrieves the stored step index from localStorage, with bounds checking.
 *
 * Returns 0 (first step) if:
 *   - Running in SSR (no window)
 *   - No stored value exists
 *   - The stored value is not a valid non-negative integer
 *   - localStorage is inaccessible
 *
 * The stored value is clamped to `max` to handle the case where steps
 * were removed since the value was saved.
 *
 * @param key - The localStorage key to read from.
 * @param max - Maximum valid step index (steps.length - 1).
 * @returns The stored step index, clamped to [0, max].
 */
function getStoredStep(key: string, max: number): number {
  if (typeof window === 'undefined') return 0;
  try {
    const stored = localStorage.getItem(key);
    if (!stored) return 0;
    const parsed = parseInt(stored, 10);
    if (isNaN(parsed) || parsed < 0) return 0;
    return Math.min(parsed, max);
  } catch {
    return 0;
  }
}

/**
 * Persists the current step index to localStorage.
 *
 * Silently catches errors since localStorage may be unavailable in
 * private browsing mode or when the storage quota is exceeded.
 *
 * @param key - The localStorage key to write to.
 * @param step - The step index to persist.
 */
function storeStep(key: string, step: number): void {
  try {
    localStorage.setItem(key, String(step));
  } catch {
    // localStorage may be unavailable (private browsing, quota exceeded)
  }
}

/* ========================================================================
 * TutorialPage Component
 * ======================================================================== */

/**
 * Renders a full interactive tutorial with step navigation, Coq editor,
 * goals panel, hints, and completion detection.
 *
 * @param props - Tutorial configuration including steps, title, storage key,
 *   and completion link.
 * @returns The complete tutorial page UI with split-panel layout.
 */
export function TutorialPage({ steps, title, storageKey, completionLink }: TutorialPageProps) {
  /** Index of the currently active tutorial step */
  const [currentStep, setCurrentStep] = useState(0);
  /** Current editor content (Coq code) */
  const [code, setCode] = useState('');
  /** Whether the current step's proof has been successfully completed */
  const [stepComplete, setStepComplete] = useState(false);
  /** Whether the hint for the current step is visible */
  const [showHint, setShowHint] = useState(false);
  /** Whether Zustand stores have hydrated from localStorage */
  const hydrated = useHydrated();

  /** Destructure Coq runtime state from the shared coqStore */
  const { goals, status, messages, reset: resetCoqStore } = useCoqStore();

  /**
   * Ref that always points to the latest editor content.
   * This allows the useCoqSession hook to read current code without
   * including `code` in its dependency arrays, which would cause the
   * Coq session to reinitialize on every keystroke.
   */
  const codeRef = useRef(code);
  useEffect(() => {
    codeRef.current = code;
  }, [code]);

  /** The current step data object */
  const step = steps[currentStep];

  /**
   * Initialize the shared Coq session hook.
   *
   * This hook manages the jsCoq iframe lifecycle and provides functions
   * for executing Coq statements (next, prev, all, reset).
   *
   * The `onGoalsUpdate` callback implements the step completion check:
   * a step is complete when goals are empty, proof was started, and Coq
   * is in 'ready' state. The three-way check (H4 fix) prevents false
   * positives during reset or mid-execution when goals are transiently empty.
   *
   * The `onAfterReset` callback restores the editor to the current step's
   * template and clears the step completion flag.
   */
  const {
    serviceRef,
    coqLoading,
    coqInitError,
    executedUpTo,
    handleExecuteNext,
    handleExecutePrev,
    handleExecuteAll,
    handleReset: baseHandleReset,
    initializeCoqService,
  } = useCoqSession(codeRef, {
    prelude: step?.exercise.prelude ?? '',
    onGoalsUpdate: useCallback((g: CoqGoal[]) => {
      /* Step completion detection (H4 fix):
         Only mark complete when ALL three conditions are met:
         1. Goals array is empty (proof is finished)
         2. Proof was actually started (not just an empty initial state)
         3. Coq service is in 'ready' state (not mid-execution)
         This prevents false positives when goals are transiently empty
         during resets or between execution steps. */
      if (g.length === 0 && serviceRef.current && serviceRef.current.isProofStarted() && serviceRef.current.getStatus() === 'ready') {
        setStepComplete(true);
      }
    // serviceRef is a stable ref object -- safe to omit from deps.
    // eslint-disable-next-line react-hooks/exhaustive-deps
    }, []),
    onAfterReset: useCallback(() => {
      setCode(steps[currentStep]?.exercise.template ?? '');
      setStepComplete(false);
    // steps is a prop that doesn't change identity for a given tutorial page.
    // currentStep is read via closure; the callback is re-created when currentStep changes
    // due to the dep below, so the closure is always fresh.
    // eslint-disable-next-line react-hooks/exhaustive-deps
    }, [currentStep, steps]),
  });

  /**
   * Restore the saved step index on mount.
   * Uses an empty dependency array to run exactly once on mount.
   * The stored step is clamped to the valid range in case steps were
   * removed since the value was saved.
   */
  useEffect(() => {
    setCurrentStep(getStoredStep(storageKey, steps.length - 1));
  // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  /**
   * Reset editor state when the step changes.
   * Loads the new step's template into the editor, clears completion
   * and hint state, and resets the Coq store (goals, messages, etc.).
   */
  useEffect(() => {
    if (!step) return;
    setCode(step.exercise.template);
    setStepComplete(false);
    setShowHint(false);
    resetCoqStore();
  // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [currentStep]);

  /**
   * Initialize the Coq service once on mount.
   * This triggers the jsCoq iframe creation and initialization sequence.
   * Uses an empty dependency array to run exactly once.
   */
  useEffect(() => {
    initializeCoqService();
  // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  /**
   * Wrapper around the base reset handler from useCoqSession.
   * Memoized to maintain stable identity for child component props.
   */
  const handleReset = useCallback(async () => {
    await baseHandleReset();
  }, [baseHandleReset]);

  /**
   * Advances to the next tutorial step.
   * Persists the new step index to localStorage so progress survives
   * page reloads. No-op if already on the last step.
   */
  const handleNextStep = useCallback(() => {
    if (currentStep < steps.length - 1) {
      const next = currentStep + 1;
      setCurrentStep(next);
      storeStep(storageKey, next);
    }
  }, [currentStep, steps.length, storageKey]);

  /**
   * Goes back to the previous tutorial step.
   * Persists the new step index to localStorage. No-op if on the first step.
   */
  const handlePrevStep = useCallback(() => {
    if (currentStep > 0) {
      const prev = currentStep - 1;
      setCurrentStep(prev);
      storeStep(storageKey, prev);
    }
  }, [currentStep, storageKey]);

  /* Loading state: show a spinner until Zustand stores have hydrated
     and the current step data is available */
  if (!hydrated || !step) {
    return (
      <div className="flex items-center justify-center h-[calc(100vh-64px)]">
        <Loader2 className="h-6 w-6 animate-spin text-muted-foreground" />
      </div>
    );
  }

  return (
    <div className="max-w-6xl mx-auto px-4 py-6 h-[calc(100vh-64px)] flex flex-col gap-4">
      {/* ================================================================
       * Step indicator header
       * Shows the tutorial title and numbered step buttons.
       * Past steps get green background, current step gets primary,
       * future steps get muted background.
       * ================================================================ */}
      <div className="flex items-center justify-between">
        <h1 className="text-xl font-bold">{title}</h1>
        <div className="flex items-center gap-2">
          {steps.map((s, i) => (
            <button
              key={i}
              onClick={() => { setCurrentStep(i); storeStep(storageKey, i); }}
              aria-label={`Step ${i + 1}: ${s.title}`}
              aria-current={i === currentStep ? 'step' : undefined}
              className={`w-8 h-8 rounded-full text-sm font-medium transition-colors ${
                i === currentStep
                  ? 'bg-primary text-primary-foreground'
                  : i < currentStep
                  ? 'bg-green-100 text-green-700 dark:bg-green-900 dark:text-green-300'
                  : 'bg-muted text-muted-foreground'
              }`}
            >
              {i + 1}
            </button>
          ))}
        </div>
      </div>

      {/* ================================================================
       * Main content area -- two-column layout on large screens
       * Left column: step explanation, hint, success message
       * Right column: Coq editor with toolbar and goals panel
       * ================================================================ */}
      <div className="flex-1 min-h-0 grid lg:grid-cols-2 gap-4">
        {/* Left panel: explanation and hints */}
        <Card className="p-6 overflow-auto">
          <h2 className="text-lg font-semibold mb-4">
            Step {step.id}: {step.title}
          </h2>
          {/* FormattedDescription renders markdown-like formatting (code blocks,
              bold, etc.) from the step's explanation text */}
          <div className="prose prose-sm dark:prose-invert max-w-none">
            <FormattedDescription text={step.explanation} />
          </div>

          {/* Hint toggle button -- hidden once hint is shown to avoid clutter */}
          {!showHint && (
            <Button variant="outline" size="sm" onClick={() => setShowHint(true)} className="mt-4 gap-1">
              <Lightbulb className="h-4 w-4" />
              Show Hint
            </Button>
          )}
          {/* Hint display -- yellow-tinted box with the hint in a code element */}
          {showHint && (
            <div className="mt-4 p-3 rounded-md bg-yellow-50 dark:bg-yellow-950/30 border border-yellow-200 dark:border-yellow-900 text-sm">
              <span className="font-medium">Hint:</span> <code className="bg-muted px-1 py-0.5 rounded text-xs">{step.hint}</code>
            </div>
          )}

          {/* Success message -- green-tinted box shown when step proof is complete */}
          {stepComplete && (
            <div className="mt-4 p-3 rounded-md bg-green-50 dark:bg-green-950/30 border border-green-200 dark:border-green-900 text-sm flex items-start gap-2">
              <CheckCircle2 className="h-4 w-4 text-green-600 mt-0.5 shrink-0" />
              <span className="text-green-700 dark:text-green-400">{step.successMessage}</span>
            </div>
          )}
        </Card>

        {/* Right panel: Coq editor, toolbar, and goals */}
        <div className="flex flex-col overflow-hidden border rounded-lg">
          {/* CoqStatusBar shows loading spinner during jsCoq initialization
              or error message if initialization failed */}
          <CoqStatusBar loading={coqLoading} error={coqInitError} />

          {/* Editor toolbar with execute/reset controls.
              canSubmit is false because tutorials don't have a "submit" action --
              completion is detected automatically via goal state monitoring. */}
          <EditorToolbar
            status={status}
            onExecuteNext={handleExecuteNext}
            onExecutePrev={handleExecutePrev}
            onExecuteAll={handleExecuteAll}
            onReset={handleReset}
            onSubmit={handleExecuteAll}
            canSubmit={false}
          />

          {/* CodeMirror-based Coq editor with syntax highlighting.
              The executedUpTo prop highlights which statements have been
              processed by the Coq engine. */}
          <div className="flex-1 min-h-0">
            <CoqEditor
              value={code}
              onChange={setCode}
              onExecuteNext={handleExecuteNext}
              onExecutePrev={handleExecutePrev}
              onExecuteAll={handleExecuteAll}
              executedUpTo={executedUpTo}
              className="h-full"
            />
          </div>

          {/* Goals panel -- shows current proof goals and Coq messages.
              Takes up the bottom third of the right panel with a minimum
              height to remain usable even on small screens. */}
          <div className="border-t h-1/3 min-h-[120px]">
            <div className="px-3 py-2 border-b bg-muted/30 text-sm font-medium">
              Goals {goals.length > 0 && `(${goals.length})`}
            </div>
            <GoalsPanel
              goals={goals}
              messages={messages}
              isLoading={status === 'busy' || status === 'loading'}
              isComplete={stepComplete}
              className="h-[calc(100%-37px)]"
            />
          </div>
        </div>
      </div>

      {/* ================================================================
       * Bottom navigation bar
       * Previous/Next buttons with the final step showing the completion
       * link instead of "Next Step".
       * ================================================================ */}
      <div className="flex items-center justify-between py-2">
        <Button
          variant="outline"
          onClick={handlePrevStep}
          disabled={currentStep === 0}
          className="gap-1"
        >
          <ArrowLeft className="h-4 w-4" />
          Previous
        </Button>

        {/* On the last step, show the completion link (e.g., "Continue to Problems")
            instead of a "Next Step" button */}
        {currentStep < steps.length - 1 ? (
          <Button onClick={handleNextStep} className="gap-1">
            Next Step
            <ArrowRight className="h-4 w-4" />
          </Button>
        ) : (
          <Link href={completionLink.href}>
            <Button className="gap-1">
              {completionLink.label}
              <ArrowRight className="h-4 w-4" />
            </Button>
          </Link>
        )}
      </div>
    </div>
  );
}
