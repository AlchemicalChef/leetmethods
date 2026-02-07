'use client';

import { useEffect, useState, useCallback, useRef, useMemo } from 'react';
import { useHydrated } from '@/hooks/useHydrated';
import { useSearchParams } from 'next/navigation';
import { ChevronDown, ChevronUp, Loader2, AlertCircle, RefreshCw } from 'lucide-react';
import { CoqEditor, GoalsPanel, EditorToolbar } from '@/components/editor';
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

interface ProblemSolverProps {
  problem: Problem;
  allProblems?: ProblemSummary[];
}

export function ProblemSolver({ problem, allProblems = [] }: ProblemSolverProps) {
  const { code, loadCode, setCode, saveCode, resetCode } = useEditorStore();
  const { goals, status, proofState, setProofState, addMessage, messages, reset: resetCoqStore, guidedMode, toggleGuidedMode } = useCoqStore();
  const { markCompleted, incrementAttempts, incrementHints, incrementReviewAttempts, incrementReviewHints, getProgress, startTimer, stopTimer, startReview, completeReview } = useProgressStore();
  const searchParams = useSearchParams();

  const { checkAndUnlock } = useAchievementChecker(allProblems);

  const [hintsRevealed, setHintsRevealed] = useState(0);
  const [submissionResult, setSubmissionResult] = useState<'success' | 'failure' | null>(null);
  const [goalsExpanded, setGoalsExpanded] = useState(true);
  const [shortcutsOpen, setShortcutsOpen] = useState(false);
  const hydrated = useHydrated();
  const isReviewMode = searchParams.get('review') === 'true';

  const codeRef = useRef(code);
  const submittingRef = useRef(false);
  const cursorPositionRef = useRef(0);

  useEffect(() => {
    codeRef.current = code;
  }, [code]);

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

  // Wrap execution handlers -- the hook handles onBeforeExecute internally,
  // so these pass through directly. Kept as named locals so the JSX reads cleanly.
  const handleExecuteNext = baseExecuteNext;
  const handleExecuteAll = baseExecuteAll;
  const handleExecuteToPosition = baseExecuteToPosition;

  const handleReset = useCallback(async () => {
    await baseHandleReset();
  }, [baseHandleReset]);

  // Initialize editor with problem template
  useEffect(() => {
    // Reset state when problem changes
    resetCoqStore();
    setSubmissionResult(null);

    loadCode(problem.slug, problem.template);

    // Set hints based on progress
    const progress = getProgress(problem.slug);
    setHintsRevealed(progress?.hintsUsed ?? 0);

    // Initialize Coq service
    initializeCoqService();

    // Start review or solve timer
    if (isReviewMode) {
      startReview(problem.slug);
    }
    startTimer(problem.slug);

    return () => {
      stopTimer(problem.slug);
    };
  // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [problem.slug, problem.template]);

  const handleCodeChange = useCallback(
    (newCode: string) => {
      setCode(newCode);
    },
    [setCode]
  );

  const handleCursorActivity = useCallback((offset: number) => {
    cursorPositionRef.current = offset;
  }, []);

  const handleExecuteToCursor = useCallback(() => {
    handleExecuteToPosition(cursorPositionRef.current);
  }, [handleExecuteToPosition]);

  const handleSubmit = useCallback(async () => {
    if (!serviceRef.current || submittingRef.current) return;
    submittingRef.current = true;
    setSubmissionResult(null);
    setProofState('in_progress');

    try {
      if (isReviewMode) {
        incrementReviewAttempts(problem.slug);
      } else {
        incrementAttempts(problem.slug);
      }
      saveCode();

      const currentCode = codeRef.current;
      const result = await serviceRef.current.verify(problem.prelude, currentCode, problem.forbiddenTactics);

      if (result.success) {
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
        checkAndUnlock();
      } else {
        setSubmissionResult('failure');
        setProofState('in_progress');

        // Show all relevant error information
        if (result.hasForbiddenTactics) {
          addMessage('error', `Forbidden tactics used: ${result.forbiddenTacticsFound.join(', ')}`);
        }

        if (result.goals.length > 0) {
          addMessage('error', `${result.goals.length} goal(s) remaining. Complete the proof to submit.`);
        }

        // Show additional errors (execution failures, Qed failures, etc.)
        if (result.errors.length > 0) {
          for (const error of result.errors) {
            // Avoid duplicate messages about goals
            if (!error.includes('goal(s) remaining')) {
              addMessage('error', error);
            }
          }
        }

        // Fallback if no specific error was shown
        if (!result.hasForbiddenTactics && result.goals.length === 0 && result.errors.length === 0) {
          addMessage('error', 'Proof verification failed. Check your code for errors.');
        }
      }
    } finally {
      submittingRef.current = false;
    }
  }, [problem, saveCode, markCompleted, incrementAttempts, incrementReviewAttempts, isReviewMode, completeReview, checkAndUnlock, addMessage, setProofState, serviceRef]);

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

  // Global ? key listener for shortcuts help
  useEffect(() => {
    const handler = (e: KeyboardEvent) => {
      if (e.key === '?' && !e.ctrlKey && !e.metaKey) {
        const target = e.target as HTMLElement;
        if (target.closest('.cm-editor')) return;
        const tagName = target.tagName.toLowerCase();
        if (tagName === 'input' || tagName === 'textarea' || target.isContentEditable) return;
        setShortcutsOpen(true);
      }
    };
    window.addEventListener('keydown', handler);
    return () => window.removeEventListener('keydown', handler);
  }, []);

  const isComplete = submissionResult === 'success' && proofState === 'completed' && goals.length === 0;

  const progress = getProgress(problem.slug);
  const solutionAvailable = hydrated && (submissionResult === 'success' || progress?.completed || (progress?.attempts ?? 0) >= 5);
  const progressMap = useProgressStore((s) => s.progress);
  const completedSlugs = useMemo(
    () => Object.values(progressMap).filter((p) => p.completed).map((p) => p.slug),
    [progressMap]
  );
  const getDueReviews = useProgressStore((s) => s.getDueReviews);
  const dueSlugs = useMemo(() => {
    try {
      return getDueReviews().map((r) => r.slug);
    } catch {
      return [];
    }
  }, [getDueReviews]);
  const nextProblem = isComplete && allProblems.length > 0
    ? getNextRecommendation(problem, allProblems, completedSlugs, dueSlugs)
    : null;

  const guidedSuggestions = useMemo(() => {
    if (!guidedMode || goals.length === 0) return [];
    return suggestTactics({ goals, forbiddenTactics: problem.forbiddenTactics });
  }, [guidedMode, goals, problem.forbiddenTactics]);

  const prerequisiteStatus = useMemo(() => {
    if (!problem.prerequisites || allProblems.length === 0) return undefined;
    return getPrerequisiteStatus(problem, completedSlugs, allProblems as Problem[]);
  }, [problem, completedSlugs, allProblems]);

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

  const editorPanel = (
    <div className="h-full flex flex-col overflow-hidden">
      {/* Status indicator */}
      {(coqLoading || coqInitError) && (
        <div className="flex items-center gap-2 px-3 py-2 border-b bg-muted/20 text-xs">
          {coqLoading ? (
            <>
              <Loader2 className="h-3 w-3 animate-spin text-muted-foreground" />
              <span className="text-muted-foreground">Initializing Coq runtime...</span>
            </>
          ) : coqInitError ? (
            <>
              <AlertCircle className="h-3 w-3 text-destructive" />
              <span className="text-destructive" title={coqInitError}>
                Failed to initialize Coq: {coqInitError}
              </span>
            </>
          ) : null}
        </div>
      )}

      {/* Toolbar */}
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

      {/* Review mode banner */}
      {isReviewMode && !submissionResult && (
        <div className="px-4 py-2 text-sm font-medium bg-amber-100 text-amber-800 dark:bg-amber-900 dark:text-amber-200 flex items-center gap-2">
          <RefreshCw className="h-3.5 w-3.5" />
          Review Mode - Solve this problem again to update your SRS schedule
        </div>
      )}

      {/* Submission result banner */}
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

      {/* Editor */}
      <div className="flex-1 min-h-0 flex flex-col">
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

        {/* Goals panel - collapsible on mobile */}
        <div className={`border-t transition-all duration-200 ${goalsExpanded ? 'h-1/3 min-h-[150px]' : 'h-auto'}`}>
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

  return (
    <div className="h-[calc(100vh-64px)]">
      {/* Desktop: resizable split */}
      <div className="hidden lg:block h-full">
        <ResizableSplit direction="horizontal" defaultRatio={0.5} minRatio={0.25} maxRatio={0.75}>
          <div className="h-full overflow-hidden flex flex-col">{descriptionPanel}</div>
          {editorPanel}
        </ResizableSplit>
      </div>

      {/* Mobile: stacked layout */}
      <div className="lg:hidden h-full flex flex-col">
        <div className="h-1/3 border-b overflow-hidden flex flex-col">{descriptionPanel}</div>
        <div className="flex-1 overflow-hidden">{editorPanel}</div>
      </div>

      <KeyboardShortcutsHelp open={shortcutsOpen} onClose={() => setShortcutsOpen(false)} />
    </div>
  );
}
