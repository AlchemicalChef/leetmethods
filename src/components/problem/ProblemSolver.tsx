'use client';

import { useEffect, useState, useCallback, useRef } from 'react';
import { ChevronDown, ChevronUp, Loader2, AlertCircle } from 'lucide-react';
import { CoqEditor, GoalsPanel, EditorToolbar } from '@/components/editor';
import { ProblemDescription } from './ProblemDescription';
import { useEditorStore } from '@/store/editorStore';
import { useCoqStore } from '@/store/coqStore';
import { useProgressStore } from '@/store/progressStore';
import { getCoqService, resetCoqService, setInitializing } from '@/lib/coq';
import type { CoqService } from '@/lib/coq';
import type { Problem } from '@/lib/problems/types';

interface ProblemSolverProps {
  problem: Problem;
}

export function ProblemSolver({ problem }: ProblemSolverProps) {
  const { code, loadCode, setCode, saveCode, resetCode } = useEditorStore();
  const { goals, setGoals, status, setStatus, proofState, setProofState, addMessage, reset: resetCoqStore } = useCoqStore();
  const { markCompleted, incrementAttempts, incrementHints, getProgress } = useProgressStore();

  const [hintsRevealed, setHintsRevealed] = useState(0);
  const [submissionResult, setSubmissionResult] = useState<'success' | 'failure' | null>(null);
  const [goalsExpanded, setGoalsExpanded] = useState(true);
  const [coqLoading, setCoqLoading] = useState(false);
  const [coqInitError, setCoqInitError] = useState<string | null>(null);

  // Use ref to capture code at execution time
  const codeRef = useRef(code);
  const serviceRef = useRef<CoqService | null>(null);

  useEffect(() => {
    codeRef.current = code;
  }, [code]);

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

    return () => {
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
    if (!serviceRef.current) return;
    incrementAttempts(problem.slug);
    saveCode();

    const currentCode = codeRef.current;
    const result = await serviceRef.current.verify(problem.prelude, currentCode, problem.forbiddenTactics);

    if (result.success) {
      markCompleted(problem.slug);
      setSubmissionResult('success');
      setProofState('completed');
      addMessage('success', 'Proof accepted! Congratulations!');
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
  }, [problem, saveCode, markCompleted, incrementAttempts, addMessage, setProofState]);

  const handleRevealHint = useCallback(() => {
    if (hintsRevealed < problem.hints.length) {
      setHintsRevealed((prev) => prev + 1);
      incrementHints(problem.slug);
    }
  }, [hintsRevealed, problem.hints.length, problem.slug, incrementHints]);

  const isComplete = proofState === 'completed' && goals.length === 0 && submissionResult !== 'failure';

  return (
    <div className="h-[calc(100vh-64px)] flex flex-col lg:flex-row">
      {/* Left panel - Problem description */}
      <div className="lg:w-1/2 h-1/3 lg:h-full border-b lg:border-b-0 lg:border-r overflow-hidden flex flex-col">
        <ProblemDescription
          problem={problem}
          hintsRevealed={hintsRevealed}
          onRevealHint={handleRevealHint}
          className="flex-1"
        />
      </div>

      {/* Right panel - Editor and goals */}
      <div className="lg:w-1/2 flex-1 lg:flex-none lg:h-full flex flex-col overflow-hidden">
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
          onReset={handleReset}
          onSubmit={handleSubmit}
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
            {submissionResult === 'success'
              ? 'Accepted! Your proof is correct.'
              : 'Not accepted. Check the errors below.'}
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
              className="h-full"
            />
          </div>

          {/* Goals panel - collapsible on mobile */}
          <div className={`border-t transition-all duration-200 ${goalsExpanded ? 'h-1/3 min-h-[150px]' : 'h-auto'}`}>
            <button
              onClick={() => setGoalsExpanded(!goalsExpanded)}
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
                isLoading={status === 'busy' || status === 'loading'}
                isComplete={isComplete}
                className="h-[calc(100%-37px)]"
              />
            )}
          </div>
        </div>
      </div>
    </div>
  );
}
