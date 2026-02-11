/**
 * @module ProblemSolver
 *
 * The main problem-solving page component that orchestrates the entire Coq proof
 * editing experience. This is the centerpiece of LeetMethods -- it combines the
 * code editor, goals panel, problem description, hints, submission flow, and
 * spaced repetition review into a single cohesive UI.
 *
 * Architecture overview:
 * ```
 * ProblemSolver
 *   ├── ProblemDescription (left/top panel)
 *   │     ├── Problem metadata, description, hints
 *   │     ├── PrerequisitesPanel (if prereqs defined)
 *   │     └── SolutionReveal (after 5 attempts or completion)
 *   └── Editor panel (right/bottom panel)
 *         ├── CoqStatusBar (initialization state)
 *         ├── EditorToolbar (execution controls + submit)
 *         ├── Review mode banner (if ?review=true)
 *         ├── Submission result banner
 *         ├── CoqEditor (CodeMirror 6)
 *         └── GoalsPanel (collapsible, with guided suggestions)
 * ```
 *
 * Key design decisions:
 *
 * 1. **Code persistence**: User code is saved to localStorage per-problem-slug
 *    via `editorStore`. When revisiting a problem, previous code is restored.
 *
 * 2. **Proof state machine**: The `proofState` transitions are explicit
 *    ('not_started' -> 'in_progress' -> 'completed') to avoid false positives.
 *    `handleSubmit` sets 'in_progress' at the start to clear stale 'completed'.
 *
 * 3. **Review mode**: Accessed via `?review=true` query param. Uses separate
 *    attempt/hint counters and updates the SRS (spaced repetition) schedule
 *    on completion rather than the initial completion flag.
 *
 * 4. **Submission guard**: `submittingRef` prevents double-submit race conditions.
 *    The ref pattern (vs state) avoids re-renders during the async flow.
 *
 * 5. **Responsive layout**: Desktop uses a resizable horizontal split (50/50 default).
 *    Mobile stacks description above editor with a collapsible goals panel.
 *
 * 6. **Next problem recommendation**: After successful submission, computes
 *    the next recommended problem based on difficulty progression, category
 *    variety, and SRS due reviews.
 *
 * 7. **Achievement checking**: After successful submission, runs achievement
 *    unlock checks (e.g., "solve 5 problems", "complete a category").
 *
 * @see {@link useCoqSession} for the Coq lifecycle management hook
 * @see {@link CoqService} for the jsCoq iframe bridge
 * @see {@link progressStore} for completion/attempt/timer persistence
 */
'use client';

import { useEffect, useState, useCallback, useRef, useMemo } from 'react';
import { useHydrated } from '@/hooks/useHydrated';
import { useSearchParams } from 'next/navigation';
import { ChevronDown, ChevronUp, RefreshCw } from 'lucide-react';
import { CoqEditor, GoalsPanel, EditorToolbar, CoqStatusBar } from '@/components/editor';
import { KeyboardShortcutsHelp } from '@/components/editor/KeyboardShortcutsHelp';
import { ProblemDescription } from './ProblemDescription';
import { ResizableSplit } from '@/components/ui/resizable-split';
import { useEditorStore } from '@/store/editorStore';
import { useCoqStore } from '@/store/coqStore';
import { useProgressStore } from '@/store/progressStore';
import { useCoqSession } from '@/hooks/useCoqSession';
import { NextProblemCard } from './NextProblemCard';
import { getNextRecommendation } from '@/lib/recommendations';
import { useAchievementChecker } from '@/hooks/useAchievementChecker';
import { suggestTactics } from '@/lib/coq/tactic-suggester';
import { getPrerequisiteStatus } from '@/lib/prerequisites';
import type { Problem, ProblemSummary } from '@/lib/problems/types';

/* ============================================================================
 * Types
 * ============================================================================ */

/**
 * Props for the ProblemSolver component.
 */
interface ProblemSolverProps {
  /** The full problem object with description, template, solution, hints, etc. */
  problem: Problem;
  /** All available problem summaries, used for next-problem recommendations */
  allProblems?: ProblemSummary[];
}

/* ============================================================================
 * ProblemSolver Component
 * ============================================================================ */

/**
 * Main problem-solving page component.
 *
 * Manages the full lifecycle of solving a Coq proof problem: initializing
 * the editor, executing code against jsCoq, handling submission and
 * verification, tracking progress, and providing hints and guidance.
 *
 * @param props - See {@link ProblemSolverProps}
 * @returns The complete problem solver UI
 */
export function ProblemSolver({ problem, allProblems = [] }: ProblemSolverProps) {
  /* --- Store hooks --- */
  const { code, loadCode, setCode, saveCode, resetCode } = useEditorStore();
  const { goals, status, proofState, setProofState, addMessage, clearMessages, messages, reset: resetCoqStore, guidedMode, toggleGuidedMode } = useCoqStore();
  const { markCompleted, incrementAttempts, incrementHints, incrementReviewAttempts, incrementReviewHints, getProgress, startTimer, stopTimer, startReview, completeReview } = useProgressStore();
  const searchParams = useSearchParams();

  /** Achievement checker -- evaluates unlock conditions after successful submissions */
  const { checkAndUnlock } = useAchievementChecker(allProblems);

  /* --- Local state --- */
  /** Number of hints currently revealed for this problem */
  const [hintsRevealed, setHintsRevealed] = useState(0);
  /** Current submission result: null (not submitted), 'success', or 'failure' */
  const [submissionResult, setSubmissionResult] = useState<'success' | 'failure' | null>(null);
  /** Whether the goals panel is expanded (mobile: collapsible) */
  const [goalsExpanded, setGoalsExpanded] = useState(true);
  /** Whether the keyboard shortcuts help dialog is open */
  const [shortcutsOpen, setShortcutsOpen] = useState(false);
  /** Whether Zustand stores have been hydrated from localStorage */
  const hydrated = useHydrated();
  /** Detect review mode via URL query parameter */
  const isReviewMode = searchParams.get('review') === 'true';

  /* --- Refs for avoiding stale closures in async callbacks --- */

  /**
   * `codeRef` keeps a stable reference to the current editor content.
   * This is passed to `useCoqSession` which needs to read the latest code
   * at execution time without depending on React state updates.
   */
  const codeRef = useRef(code);
  /**
   * `submittingRef` prevents double-submission. Using a ref instead of state
   * avoids unnecessary re-renders during the async verification flow.
   */
  const submittingRef = useRef(false);
  /** Tracks the current cursor offset for execute-to-cursor functionality */
  const cursorPositionRef = useRef(0);

  /** Keep codeRef in sync with the latest editor content */
  useEffect(() => {
    codeRef.current = code;
  }, [code]);

  /* --- Coq session lifecycle --- */

  /**
   * Initialize the Coq session via the shared `useCoqSession` hook.
   *
   * The hook manages the CoqService singleton lifecycle, including:
   * - Creating/reusing the jsCoq iframe
   * - Executing statements step-by-step
   * - Tracking the executed-up-to offset for highlighting
   * - Resetting Coq state on demand
   *
   * Callbacks:
   * - `onBeforeExecute`: Sets proof state to 'in_progress' before any execution
   * - `onAfterReset`: Restores the problem template and clears submission state
   */
  const {
    serviceRef,
    coqLoading,
    coqInitError,
    executedUpTo,
    handleExecuteNext: baseExecuteNext,
    handleExecutePrev,
    handleExecuteAll: baseExecuteAll,
    handleExecuteToPosition: baseExecuteToPosition,
    handleReset: baseHandleReset,
    initializeCoqService,
  } = useCoqSession(codeRef, {
    prelude: problem.prelude,
    onBeforeExecute: useCallback(() => {
      setProofState('in_progress');
    }, [setProofState]),
    onAfterReset: useCallback(() => {
      resetCode(problem.template);
      setSubmissionResult(null);
      setProofState('not_started');
    }, [problem.template, resetCode, setProofState]),
  });

  /**
   * Wrap execution handlers as named locals for cleaner JSX.
   * The hook handles onBeforeExecute internally, so these pass through directly.
   */
  const handleExecuteNext = baseExecuteNext;
  const handleExecuteAll = baseExecuteAll;
  const handleExecuteToPosition = baseExecuteToPosition;

  /** Wrap reset to ensure it's always awaited */
  const handleReset = useCallback(async () => {
    await baseHandleReset();
  }, [baseHandleReset]);

  /* --- Problem initialization --- */

  /**
   * Initialize editor and Coq state when the problem changes.
   *
   * This effect runs when `problem.slug` or `problem.template` changes (i.e.,
   * navigating to a different problem). It:
   * 1. Resets the Coq store (clears goals, messages, proof state)
   * 2. Loads saved code for this problem (or uses the template if no save exists)
   * 3. Restores hint reveal count from progress
   * 4. Initializes the CoqService singleton
   * 5. Starts the solve/review timer for time tracking
   */
  useEffect(() => {
    resetCoqStore();
    setSubmissionResult(null);

    loadCode(problem.slug, problem.template);

    // Restore previously revealed hints from progress store
    const progress = getProgress(problem.slug);
    setHintsRevealed(progress?.hintsUsed ?? 0);

    initializeCoqService();

    // Start SRS review session if in review mode
    if (isReviewMode) {
      startReview(problem.slug);
    }
    startTimer(problem.slug);

    return () => {
      stopTimer(problem.slug);
    };
  // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [problem.slug, problem.template]);

  /* --- Event handlers --- */

  /**
   * Handle user edits to the code.
   * Clears any previous submission result when the user starts editing again,
   * since the old result no longer applies to the modified code.
   */
  const handleCodeChange = useCallback(
    (newCode: string) => {
      setCode(newCode);
      if (submissionResult) {
        setSubmissionResult(null);
        clearMessages();
      }
    },
    [setCode, submissionResult, clearMessages]
  );

  /** Track cursor position for the execute-to-cursor feature */
  const handleCursorActivity = useCallback((offset: number) => {
    cursorPositionRef.current = offset;
  }, []);

  /** Execute statements up to the current cursor position */
  const handleExecuteToCursor = useCallback(() => {
    handleExecuteToPosition(cursorPositionRef.current);
  }, [handleExecuteToPosition]);

  /**
   * Submit the proof for full verification.
   *
   * This is the core submission flow:
   * 1. Guard against double-submit via `submittingRef`
   * 2. Increment attempt counter (separate counters for review mode)
   * 3. Save the current code to localStorage
   * 4. Call `CoqService.verify()` which executes the full prelude + code and
   *    checks for forbidden tactics, remaining goals, and execution errors
   * 5. On success: mark completed, update SRS, trigger achievement checks
   * 6. On failure: display specific error messages (forbidden tactics, remaining
   *    goals, execution errors) with a fallback generic message
   */
  const handleSubmit = useCallback(async () => {
    if (!serviceRef.current || submittingRef.current) return;
    submittingRef.current = true;
    setSubmissionResult(null);
    // Set in_progress to clear any stale 'completed' state from a previous attempt
    setProofState('in_progress');

    try {
      // Track attempts separately for initial solve vs. review
      if (isReviewMode) {
        incrementReviewAttempts(problem.slug);
      } else {
        incrementAttempts(problem.slug);
      }
      saveCode();

      const currentCode = codeRef.current;
      const result = await serviceRef.current.verify(problem.prelude, currentCode, problem.forbiddenTactics);

      if (result.success) {
        // Handle successful verification
        if (isReviewMode) {
          completeReview(problem.slug);
          addMessage('success', 'Review completed! Your SRS schedule has been updated.');
        } else {
          markCompleted(problem.slug);
        }
        setSubmissionResult('success');
        setProofState('completed');
        if (!isReviewMode) {
          addMessage('success', 'Proof accepted! Congratulations!');
        }
        // Check if any achievements were unlocked by this completion
        checkAndUnlock();
      } else {
        // Handle verification failure
        setSubmissionResult('failure');
        setProofState('in_progress');

        // Show all relevant error information to help the user debug
        if (result.hasForbiddenTactics) {
          addMessage('error', `Forbidden tactics used: ${result.forbiddenTacticsFound.join(', ')}`);
        }

        if (result.goals.length > 0) {
          addMessage('error', `${result.goals.length} goal(s) remaining. Complete the proof to submit.`);
        }

        // Show additional errors (execution failures, Qed failures, etc.)
        if (result.errors.length > 0) {
          for (const error of result.errors) {
            // Avoid duplicate messages about goals (already shown above)
            if (!error.includes('goal(s) remaining')) {
              addMessage('error', error);
            }
          }
        }

        // Fallback if no specific error was identified
        if (!result.hasForbiddenTactics && result.goals.length === 0 && result.errors.length === 0) {
          addMessage('error', 'Proof verification failed. Check your code for errors.');
        }
      }
    } finally {
      submittingRef.current = false;
    }
  }, [problem, saveCode, markCompleted, incrementAttempts, incrementReviewAttempts, isReviewMode, completeReview, checkAndUnlock, addMessage, setProofState, serviceRef]);

  /**
   * Reveal the next hint for the current problem.
   * Tracks hint usage in progress store for analytics (separate counters
   * for review mode to avoid inflating initial-solve hint counts).
   */
  const handleRevealHint = useCallback(() => {
    if (hintsRevealed < problem.hints.length) {
      setHintsRevealed((prev) => prev + 1);
      if (isReviewMode) {
        incrementReviewHints(problem.slug);
      } else {
        incrementHints(problem.slug);
      }
    }
  }, [hintsRevealed, problem.hints.length, problem.slug, isReviewMode, incrementHints, incrementReviewHints]);

  /* --- Global keyboard listener for shortcuts help --- */

  /**
   * Listen for the '?' key to open the keyboard shortcuts dialog.
   * Ignores the key when:
   * - Inside the CodeMirror editor (handled by CM's own keymap)
   * - Inside any input, textarea, or contentEditable element
   * - When Ctrl/Cmd is held (could be a different shortcut)
   */
  useEffect(() => {
    const handler = (e: KeyboardEvent) => {
      if (e.key === '?' && !e.ctrlKey && !e.metaKey) {
        const target = e.target as HTMLElement;
        // Don't intercept when user is typing in the CodeMirror editor
        if (target.closest('.cm-editor')) return;
        // Don't intercept when user is typing in native inputs
        const tagName = target.tagName.toLowerCase();
        if (tagName === 'input' || tagName === 'textarea' || target.isContentEditable) return;
        setShortcutsOpen(true);
      }
    };
    window.addEventListener('keydown', handler);
    return () => window.removeEventListener('keydown', handler);
  }, []);

  /* --- Derived state --- */

  /**
   * Proof is considered complete only when all three conditions are met:
   * submission succeeded AND proof state is 'completed' AND no goals remain.
   * This triple-check prevents false positives from stale state.
   */
  const isComplete = submissionResult === 'success' && proofState === 'completed' && goals.length === 0;

  /**
   * Determine if the reference solution should be available.
   * The solution is shown if:
   * - The user just successfully submitted
   * - The user has previously completed this problem
   * - The user has attempted at least 5 times (mercy rule)
   */
  const progress = getProgress(problem.slug);
  const solutionAvailable = hydrated && (submissionResult === 'success' || progress?.completed || (progress?.attempts ?? 0) >= 5);

  /**
   * Compute completed slugs for next-problem recommendations and prereq checks.
   * Uses progressMap from the store to build a derived list.
   */
  const progressMap = useProgressStore((s) => s.progress);
  const completedSlugs = useMemo(
    () => Object.values(progressMap).filter((p) => p.completed).map((p) => p.slug),
    [progressMap]
  );

  /**
   * Compute due SRS reviews for next-problem recommendations.
   * The progressMap dependency ensures recomputation when progress changes.
   */
  const getDueReviews = useProgressStore((s) => s.getDueReviews);
  /* eslint-disable react-hooks/exhaustive-deps -- progressMap triggers recomputation */
  const dueSlugs = useMemo(() => {
    try {
      return getDueReviews().map((r) => r.slug);
    } catch {
      return [];
    }
  }, [getDueReviews, progressMap]);
  /* eslint-enable react-hooks/exhaustive-deps */

  /**
   * Compute the next recommended problem after successful completion.
   * Only calculated when the proof is complete and problem list is available.
   */
  const nextProblem = isComplete && allProblems.length > 0
    ? getNextRecommendation(problem, allProblems, completedSlugs, dueSlugs)
    : null;

  /**
   * Compute guided mode tactic suggestions based on current goals.
   * Only computed when guided mode is active and there are goals to analyze.
   * Respects the problem's forbidden tactics list to avoid suggesting them.
   */
  const guidedSuggestions = useMemo(() => {
    if (!guidedMode || goals.length === 0) return [];
    return suggestTactics({ goals, forbiddenTactics: problem.forbiddenTactics });
  }, [guidedMode, goals, problem.forbiddenTactics]);

  /**
   * Compute prerequisite satisfaction status for this problem.
   * Shows which prerequisite problems need to be solved first and which
   * concepts need to be learned.
   */
  const prerequisiteStatus = useMemo(() => {
    if (!problem.prerequisites || allProblems.length === 0) return undefined;
    return getPrerequisiteStatus(problem, completedSlugs, allProblems as Problem[]);
  }, [problem, completedSlugs, allProblems]);

  /* --- Panel rendering --- */

  /** Left panel (desktop) / top panel (mobile): problem description with hints */
  const descriptionPanel = (
    <ProblemDescription
      problem={problem}
      hintsRevealed={hintsRevealed}
      onRevealHint={handleRevealHint}
      solutionAvailable={solutionAvailable}
      prerequisiteStatus={prerequisiteStatus}
      className="flex-1"
    />
  );

  /** Right panel (desktop) / bottom panel (mobile): editor + toolbar + goals */
  const editorPanel = (
    <div className="h-full flex flex-col overflow-hidden">
      {/* jsCoq initialization status indicator */}
      <CoqStatusBar loading={coqLoading} error={coqInitError} errorPrefix="Failed to initialize Coq: " />

      {/* Execution controls toolbar */}
      <EditorToolbar
        status={status}
        onExecuteNext={handleExecuteNext}
        onExecutePrev={handleExecutePrev}
        onExecuteAll={handleExecuteAll}
        onExecuteToCursor={handleExecuteToCursor}
        onReset={handleReset}
        onSubmit={handleSubmit}
        onShowShortcuts={() => setShortcutsOpen(true)}
        canSubmit={status === 'ready' || status === 'error'}
        guidedMode={guidedMode}
        onToggleGuidedMode={toggleGuidedMode}
      />

      {/* Review mode banner -- shown when solving via SRS review */}
      {isReviewMode && !submissionResult && (
        <div className="px-4 py-2 text-sm font-medium bg-amber-100 text-amber-800 dark:bg-amber-900 dark:text-amber-200 flex items-center gap-2">
          <RefreshCw className="h-3.5 w-3.5" />
          Review Mode - Solve this problem again to update your SRS schedule
        </div>
      )}

      {/* Submission result banner -- success or failure feedback */}
      {submissionResult && (
        <div
          className={`px-4 py-2 text-sm font-medium ${
            submissionResult === 'success'
              ? 'bg-green-100 text-green-800 dark:bg-green-900 dark:text-green-200'
              : 'bg-red-100 text-red-800 dark:bg-red-900 dark:text-red-200'
          }`}
        >
          {submissionResult === 'success' ? (
            <div className="flex items-center justify-between flex-wrap gap-2">
              <span>Accepted! Your proof is correct.</span>
              {nextProblem && <NextProblemCard problem={nextProblem} />}
            </div>
          ) : (
            'Not accepted. Check the errors below.'
          )}
        </div>
      )}

      {/* Editor and goals in a flex column that fills remaining space */}
      <div className="flex-1 min-h-0 flex flex-col">
        {/* CodeMirror editor */}
        <div className="flex-1 min-h-0">
          <CoqEditor
            value={code}
            onChange={handleCodeChange}
            onExecuteNext={handleExecuteNext}
            onExecutePrev={handleExecutePrev}
            onExecuteAll={handleExecuteAll}
            onExecuteToPosition={handleExecuteToPosition}
            onCursorActivity={handleCursorActivity}
            executedUpTo={executedUpTo}
            className="h-full"
          />
        </div>

        {/* Goals panel -- collapsible on mobile, always visible on desktop */}
        <div className={`border-t transition-all duration-200 ${goalsExpanded ? 'h-1/3 min-h-[150px]' : 'h-auto'}`}>
          {/* Collapsible header button -- clickable on mobile, static on desktop */}
          <button
            onClick={() => setGoalsExpanded(!goalsExpanded)}
            aria-label={goalsExpanded ? 'Collapse goals panel' : 'Expand goals panel'}
            className="w-full px-3 py-2 border-b bg-muted/30 text-sm font-medium flex items-center justify-between hover:bg-muted/50 transition-colors lg:cursor-default"
          >
            <span>Goals {goals.length > 0 && `(${goals.length})`}</span>
            <span className="lg:hidden">
              {goalsExpanded ? <ChevronDown className="h-4 w-4" /> : <ChevronUp className="h-4 w-4" />}
            </span>
          </button>
          {goalsExpanded && (
            <GoalsPanel
              goals={goals}
              messages={messages}
              isLoading={status === 'busy' || status === 'loading'}
              isComplete={isComplete}
              nextProblem={nextProblem}
              guidedSuggestions={guidedMode ? guidedSuggestions : undefined}
              className="h-[calc(100%-37px)]"
            />
          )}
        </div>
      </div>
    </div>
  );

  /* --- Layout --- */

  return (
    <div className="h-[calc(100vh-64px)]">
      {/* Desktop layout: side-by-side resizable panels */}
      <div className="hidden lg:block h-full">
        <ResizableSplit direction="horizontal" defaultRatio={0.5} minRatio={0.25} maxRatio={0.75}>
          <div className="h-full overflow-hidden flex flex-col">{descriptionPanel}</div>
          {editorPanel}
        </ResizableSplit>
      </div>

      {/* Mobile layout: vertically stacked panels */}
      <div className="lg:hidden h-full flex flex-col">
        <div className="h-1/3 border-b overflow-hidden flex flex-col">{descriptionPanel}</div>
        <div className="flex-1 overflow-hidden">{editorPanel}</div>
      </div>

      {/* Keyboard shortcuts help modal */}
      <KeyboardShortcutsHelp open={shortcutsOpen} onClose={() => setShortcutsOpen(false)} />
    </div>
  );
}
