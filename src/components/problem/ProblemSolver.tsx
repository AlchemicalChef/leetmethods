'use client';

import { useEffect, useState, useCallback, useRef, useMemo } from 'react';
import { ChevronDown, ChevronUp, Loader2, AlertCircle } from 'lucide-react';
import { CoqEditor, GoalsPanel, EditorToolbar } from '@/components/editor';
import { KeyboardShortcutsHelp } from '@/components/editor/KeyboardShortcutsHelp';
import { ProblemDescription } from './ProblemDescription';
import { ResizableSplit } from '@/components/ui/resizable-split';
import { useEditorStore } from '@/store/editorStore';
import { useCoqStore } from '@/store/coqStore';
import { useProgressStore } from '@/store/progressStore';
import { getCoqService, resetCoqService, setInitializing } from '@/lib/coq';
import type { CoqService } from '@/lib/coq';
import { NextProblemCard } from './NextProblemCard';
import { getNextRecommendation } from '@/lib/recommendations';
import { useAchievementChecker } from '@/hooks/useAchievementChecker';
import type { Problem, ProblemSummary } from '@/lib/problems/types';

interface ProblemSolverProps {
  problem: Problem;
  allProblems?: ProblemSummary[];
}

export function ProblemSolver({ problem, allProblems = [] }: ProblemSolverProps) {
  const { code, loadCode, setCode, saveCode, resetCode } = useEditorStore();
  const { goals, setGoals, status, setStatus, proofState, setProofState, addMessage, messages, reset: resetCoqStore } = useCoqStore();
  const { markCompleted, incrementAttempts, incrementHints, getProgress, startTimer, stopTimer } = useProgressStore();

  const { checkAndUnlock } = useAchievementChecker(allProblems);

  const [hintsRevealed, setHintsRevealed] = useState(0);
  const [submissionResult, setSubmissionResult] = useState<'success' | 'failure' | null>(null);
  const [goalsExpanded, setGoalsExpanded] = useState(true);
  const [coqLoading, setCoqLoading] = useState(false);
  const [coqInitError, setCoqInitError] = useState<string | null>(null);
  const [shortcutsOpen, setShortcutsOpen] = useState(false);
  const [executedUpTo, setExecutedUpTo] = useState(0);
  const [hydrated, setHydrated] = useState(false);

  // Use refs to capture values at execution time (avoid stale closures)
  const codeRef = useRef(code);
  const serviceRef = useRef<CoqService | null>(null);
  const preludeRef = useRef(problem.prelude);
  const submittingRef = useRef(false);
  const cursorPositionRef = useRef(0);

  useEffect(() => {
    codeRef.current = code;
  }, [code]);

  useEffect(() => {
    preludeRef.current = problem.prelude;
  }, [problem.prelude]);

  // Initialize Coq service
  const initializeCoqService = useCallback(async () => {
    setCoqLoading(true);
    setCoqInitError(null);
    setInitializing(true);

    try {
      const service = getCoqService({
        onStatusChange: setStatus,
        onGoalsUpdate: setGoals,
        onMessage: (msg) => addMessage(msg.type, msg.content),
        onPositionChange: (charOffset) => {
          // Subtract prelude length (prelude + \n\n) to get editor-relative offset
          // Use ref to always get the current problem's prelude length
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
      const errorMsg = error instanceof Error ? error.message : 'Failed to initialize Coq';
      setCoqInitError(errorMsg);
      setCoqLoading(false);
      setInitializing(false);
    }
  // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [setStatus, setGoals, addMessage]);

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

    // Start solve timer
    startTimer(problem.slug);

    return () => {
      stopTimer(problem.slug);
      resetCoqService();
    };
  // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [problem.slug, problem.template]);

  const handleCodeChange = useCallback(
    (newCode: string) => {
      setCode(newCode);
    },
    [setCode]
  );

  const handleExecuteNext = useCallback(async () => {
    if (!serviceRef.current) return;
    try {
      const currentCode = codeRef.current;
      serviceRef.current.setCode(problem.prelude + '\n\n' + currentCode);
      setProofState('in_progress');
      await serviceRef.current.executeNext();
    } catch (error) {
      console.error('[ProblemSolver] executeNext failed:', error);
      addMessage('error', error instanceof Error ? error.message : 'Execution failed');
    }
  }, [problem.prelude, setProofState, addMessage]);

  const handleExecutePrev = useCallback(async () => {
    if (!serviceRef.current) return;
    try {
      await serviceRef.current.executePrev();
    } catch (error) {
      console.error('[ProblemSolver] executePrev failed:', error);
      addMessage('error', error instanceof Error ? error.message : 'Undo failed');
    }
  }, [addMessage]);

  const handleCursorActivity = useCallback((offset: number) => {
    cursorPositionRef.current = offset;
  }, []);

  const handleExecuteToPosition = useCallback(async (charOffset: number) => {
    if (!serviceRef.current) return;
    try {
      const currentCode = codeRef.current;
      serviceRef.current.setCode(problem.prelude + '\n\n' + currentCode);
      setProofState('in_progress');
      const preludeLen = problem.prelude.length + 2;
      await serviceRef.current.executeToPosition(charOffset + preludeLen);
    } catch (error) {
      console.error('[ProblemSolver] executeToPosition failed:', error);
      addMessage('error', error instanceof Error ? error.message : 'Execution failed');
    }
  }, [problem.prelude, setProofState, addMessage]);

  const handleExecuteToCursor = useCallback(() => {
    handleExecuteToPosition(cursorPositionRef.current);
  }, [handleExecuteToPosition]);

  const handleExecuteAll = useCallback(async () => {
    if (!serviceRef.current) return;
    try {
      const currentCode = codeRef.current;
      serviceRef.current.setCode(problem.prelude + '\n\n' + currentCode);
      setProofState('in_progress');
      await serviceRef.current.executeAll();
    } catch (error) {
      console.error('[ProblemSolver] executeAll failed:', error);
      addMessage('error', error instanceof Error ? error.message : 'Execution failed');
    }
  }, [problem.prelude, setProofState, addMessage]);

  const handleReset = useCallback(async () => {
    if (!serviceRef.current) return;
    try {
      await serviceRef.current.reset();
      resetCode(problem.template);
      setSubmissionResult(null);
      setProofState('not_started');
    } catch (error) {
      console.error('[ProblemSolver] reset failed:', error);
      addMessage('error', error instanceof Error ? error.message : 'Reset failed');
    }
  }, [problem.template, resetCode, setProofState, addMessage]);

  const handleSubmit = useCallback(async () => {
    if (!serviceRef.current || submittingRef.current) return;
    submittingRef.current = true;
    setSubmissionResult(null);

    try {
      incrementAttempts(problem.slug);
      saveCode();

      const currentCode = codeRef.current;
      const result = await serviceRef.current.verify(problem.prelude, currentCode, problem.forbiddenTactics);

      if (result.success) {
        markCompleted(problem.slug);
        setSubmissionResult('success');
        setProofState('completed');
        addMessage('success', 'Proof accepted! Congratulations!');
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
  // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [problem, saveCode, markCompleted, incrementAttempts, addMessage, setProofState]);

  const handleRevealHint = useCallback(() => {
    if (hintsRevealed < problem.hints.length) {
      setHintsRevealed((prev) => prev + 1);
      incrementHints(problem.slug);
    }
  }, [hintsRevealed, problem.hints.length, problem.slug, incrementHints]);

  // Wait for client hydration before reading persisted store values
  useEffect(() => {
    setHydrated(true);
  }, []);

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
  const nextProblem = isComplete && allProblems.length > 0
    ? getNextRecommendation(problem, allProblems, completedSlugs)
    : null;

  const descriptionPanel = (
    <ProblemDescription
      problem={problem}
      hintsRevealed={hintsRevealed}
      onRevealHint={handleRevealHint}
      solutionAvailable={solutionAvailable}
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
      />

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
