'use client';

import { useEffect, useState, useCallback, useRef } from 'react';
import { CoqEditor, GoalsPanel, EditorToolbar } from '@/components/editor';
import { ProblemDescription } from './ProblemDescription';
import { useEditorStore } from '@/store/editorStore';
import { useCoqStore } from '@/store/coqStore';
import { useProgressStore } from '@/store/progressStore';
import { getCoqService, resetCoqService } from '@/lib/coq';
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

  // FIX #4: Use ref to capture code at execution time
  const codeRef = useRef(code);
  useEffect(() => {
    codeRef.current = code;
  }, [code]);

  // Initialize editor with problem template
  useEffect(() => {
    // Reset state when problem changes
    resetCoqStore();
    setSubmissionResult(null);

    loadCode(problem.slug, problem.template);

    // FIX #10: Always set hints based on progress, defaulting to 0
    const progress = getProgress(problem.slug);
    setHintsRevealed(progress?.hintsUsed ?? 0);

    // Initialize Coq service with fresh callbacks
    const service = getCoqService({
      onStatusChange: setStatus,
      onGoalsUpdate: setGoals,
      onMessage: (msg) => addMessage(msg.type, msg.content),
      onReady: () => setStatus('ready'),
    });

    service.initialize().catch(console.error);

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

  // FIX #4: Capture code atomically at execution time
  const handleExecuteNext = useCallback(async () => {
    const currentCode = codeRef.current;
    const service = getCoqService();
    service.setCode(problem.prelude + '\n\n' + currentCode);
    setProofState('in_progress');
    await service.executeNext();
  }, [problem.prelude, setProofState]);

  const handleExecutePrev = useCallback(async () => {
    const service = getCoqService();
    await service.executePrev();
  }, []);

  const handleExecuteAll = useCallback(async () => {
    const currentCode = codeRef.current;
    const service = getCoqService();
    service.setCode(problem.prelude + '\n\n' + currentCode);
    setProofState('in_progress');
    await service.executeAll();
  }, [problem.prelude, setProofState]);

  const handleReset = useCallback(async () => {
    const service = getCoqService();
    await service.reset();
    resetCode(problem.template);
    setSubmissionResult(null);
    setProofState('not_started');
  }, [problem.template, resetCode, setProofState]);

  const handleSubmit = useCallback(async () => {
    incrementAttempts(problem.slug);
    saveCode();

    const currentCode = codeRef.current;
    const service = getCoqService();
    const result = await service.verify(problem.prelude, currentCode, problem.forbiddenTactics);

    if (result.success) {
      markCompleted(problem.slug);
      setSubmissionResult('success');
      setProofState('completed');
      addMessage('success', 'Proof accepted! Congratulations!');
    } else {
      setSubmissionResult('failure');

      if (result.hasForbiddenTactics) {
        addMessage('error', `Forbidden tactics used: ${result.forbiddenTacticsFound.join(', ')}`);
      } else if (result.goals.length > 0) {
        addMessage('error', `${result.goals.length} goal(s) remaining. Complete the proof to submit.`);
      } else if (result.errors.length > 0) {
        addMessage('error', result.errors.join('\n'));
      }
    }
  }, [problem, saveCode, markCompleted, incrementAttempts, addMessage, setProofState]);

  const handleRevealHint = useCallback(() => {
    if (hintsRevealed < problem.hints.length) {
      setHintsRevealed((prev) => prev + 1);
      incrementHints(problem.slug);
    }
  }, [hintsRevealed, problem.hints.length, problem.slug, incrementHints]);

  // FIX #11: Use explicit proofState for completion check
  const isComplete = proofState === 'completed' && goals.length === 0;

  return (
    <div className="h-[calc(100vh-64px)] flex">
      {/* Left panel - Problem description */}
      <div className="w-1/2 border-r overflow-hidden flex flex-col">
        <ProblemDescription
          problem={problem}
          hintsRevealed={hintsRevealed}
          onRevealHint={handleRevealHint}
          className="flex-1"
        />
      </div>

      {/* Right panel - Editor and goals */}
      <div className="w-1/2 flex flex-col overflow-hidden">
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
              ? '✓ Accepted! Your proof is correct.'
              : '✗ Not accepted. Check the errors below.'}
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

          {/* Goals panel */}
          <div className="h-1/3 min-h-[150px] border-t">
            <div className="px-3 py-2 border-b bg-muted/30 text-sm font-medium">
              Goals
            </div>
            <GoalsPanel
              goals={goals}
              isLoading={status === 'busy' || status === 'loading'}
              isComplete={isComplete}
              className="h-[calc(100%-37px)]"
            />
          </div>
        </div>
      </div>
    </div>
  );
}
