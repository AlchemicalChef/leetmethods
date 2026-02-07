'use client';

import { useEffect, useState, useCallback, useRef } from 'react';
import { ArrowLeft, ArrowRight, CheckCircle2, Lightbulb, Loader2, AlertCircle } from 'lucide-react';
import { Button } from '@/components/ui/button';
import { Card } from '@/components/ui/card';
import { CoqEditor, GoalsPanel, EditorToolbar } from '@/components/editor';
import { getCoqService, resetCoqService, setInitializing } from '@/lib/coq';
import type { CoqService } from '@/lib/coq';
import { useCoqStore } from '@/store/coqStore';
import { tutorialSteps } from '@/lib/tutorial/tutorial-steps';
import Link from 'next/link';

const STORAGE_KEY = 'leetmethods-tutorial-progress';

function getStoredStep(): number {
  if (typeof window === 'undefined') return 0;
  const stored = localStorage.getItem(STORAGE_KEY);
  return stored ? Math.min(parseInt(stored, 10), tutorialSteps.length - 1) : 0;
}

function storeStep(step: number): void {
  localStorage.setItem(STORAGE_KEY, String(step));
}

export function TutorialPage() {
  const [currentStep, setCurrentStep] = useState(0);
  const [code, setCode] = useState('');
  const [executedUpTo, setExecutedUpTo] = useState(0);
  const [stepComplete, setStepComplete] = useState(false);
  const [showHint, setShowHint] = useState(false);
  const [coqLoading, setCoqLoading] = useState(false);
  const [coqInitError, setCoqInitError] = useState<string | null>(null);
  const [hydrated, setHydrated] = useState(false);

  const { goals, setGoals, status, setStatus, messages, addMessage, reset: resetCoqStore } = useCoqStore();

  const serviceRef = useRef<CoqService | null>(null);
  const codeRef = useRef(code);

  useEffect(() => {
    codeRef.current = code;
  }, [code]);

  useEffect(() => {
    setHydrated(true);
    setCurrentStep(getStoredStep());
  }, []);

  const step = tutorialSteps[currentStep];

  // Initialize code when step changes
  useEffect(() => {
    if (!step) return;
    setCode(step.exercise.template);
    setStepComplete(false);
    setShowHint(false);
    setExecutedUpTo(0);
    resetCoqStore();
  // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [currentStep]);

  // Initialize Coq service
  useEffect(() => {
    setCoqLoading(true);
    setCoqInitError(null);
    setInitializing(true);

    const service = getCoqService({
      onStatusChange: setStatus,
      onGoalsUpdate: (g) => {
        setGoals(g);
        // Check if proof is complete (no goals after execution)
        if (g.length === 0 && serviceRef.current && serviceRef.current.isProofStarted()) {
          setStepComplete(true);
        }
      },
      onMessage: (msg) => addMessage(msg.type, msg.content),
      onPositionChange: (charOffset) => {
        const preludeLen = (step?.exercise.prelude.length ?? 0) + 2;
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

    service.initialize().then(() => {
      serviceRef.current = service;
      setCoqLoading(false);
      setInitializing(false);
    }).catch((error) => {
      setCoqInitError(error instanceof Error ? error.message : 'Failed to initialize Coq');
      setCoqLoading(false);
      setInitializing(false);
    });

    return () => {
      resetCoqService();
    };
  // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  const handleExecuteNext = useCallback(async () => {
    if (!serviceRef.current || !step) return;
    try {
      serviceRef.current.setCode(step.exercise.prelude + '\n\n' + codeRef.current);
      await serviceRef.current.executeNext();
    } catch (error) {
      addMessage('error', error instanceof Error ? error.message : 'Execution failed');
    }
  }, [step, addMessage]);

  const handleExecutePrev = useCallback(async () => {
    if (!serviceRef.current) return;
    try {
      await serviceRef.current.executePrev();
    } catch (error) {
      addMessage('error', error instanceof Error ? error.message : 'Undo failed');
    }
  }, [addMessage]);

  const handleExecuteAll = useCallback(async () => {
    if (!serviceRef.current || !step) return;
    try {
      serviceRef.current.setCode(step.exercise.prelude + '\n\n' + codeRef.current);
      await serviceRef.current.executeAll();
    } catch (error) {
      addMessage('error', error instanceof Error ? error.message : 'Execution failed');
    }
  }, [step, addMessage]);

  const handleReset = useCallback(async () => {
    if (!serviceRef.current || !step) return;
    try {
      await serviceRef.current.reset();
      setCode(step.exercise.template);
      setStepComplete(false);
      setExecutedUpTo(0);
    } catch (error) {
      addMessage('error', error instanceof Error ? error.message : 'Reset failed');
    }
  }, [step, addMessage]);

  const handleNextStep = useCallback(() => {
    if (currentStep < tutorialSteps.length - 1) {
      const next = currentStep + 1;
      setCurrentStep(next);
      storeStep(next);
    }
  }, [currentStep]);

  const handlePrevStep = useCallback(() => {
    if (currentStep > 0) {
      const prev = currentStep - 1;
      setCurrentStep(prev);
      storeStep(prev);
    }
  }, [currentStep]);

  if (!hydrated || !step) {
    return (
      <div className="flex items-center justify-center h-[calc(100vh-64px)]">
        <Loader2 className="h-6 w-6 animate-spin text-muted-foreground" />
      </div>
    );
  }

  return (
    <div className="max-w-6xl mx-auto px-4 py-6 h-[calc(100vh-64px)] flex flex-col gap-4">
      {/* Step indicator */}
      <div className="flex items-center justify-between">
        <h1 className="text-xl font-bold">Interactive Tutorial</h1>
        <div className="flex items-center gap-2">
          {tutorialSteps.map((_, i) => (
            <button
              key={i}
              onClick={() => { setCurrentStep(i); storeStep(i); }}
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

      {/* Main content */}
      <div className="flex-1 min-h-0 grid lg:grid-cols-2 gap-4">
        {/* Left: explanation */}
        <Card className="p-6 overflow-auto">
          <h2 className="text-lg font-semibold mb-4">
            Step {step.id}: {step.title}
          </h2>
          <div className="prose prose-sm dark:prose-invert max-w-none">
            {step.explanation.split('\n\n').map((paragraph, i) => (
              <p key={i} className="mb-3 text-sm leading-relaxed">
                {formatText(paragraph)}
              </p>
            ))}
          </div>

          {/* Hint toggle */}
          {!showHint && (
            <Button variant="outline" size="sm" onClick={() => setShowHint(true)} className="mt-4 gap-1">
              <Lightbulb className="h-4 w-4" />
              Show Hint
            </Button>
          )}
          {showHint && (
            <div className="mt-4 p-3 rounded-md bg-yellow-50 dark:bg-yellow-950/30 border border-yellow-200 dark:border-yellow-900 text-sm">
              <span className="font-medium">Hint:</span> <code className="bg-muted px-1 py-0.5 rounded text-xs">{step.hint}</code>
            </div>
          )}

          {/* Success message */}
          {stepComplete && (
            <div className="mt-4 p-3 rounded-md bg-green-50 dark:bg-green-950/30 border border-green-200 dark:border-green-900 text-sm flex items-start gap-2">
              <CheckCircle2 className="h-4 w-4 text-green-600 mt-0.5 shrink-0" />
              <span className="text-green-700 dark:text-green-400">{step.successMessage}</span>
            </div>
          )}
        </Card>

        {/* Right: editor + goals */}
        <div className="flex flex-col overflow-hidden border rounded-lg">
          {/* Coq status */}
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
                  <span className="text-destructive">{coqInitError}</span>
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
            onSubmit={handleExecuteAll}
            canSubmit={false}
          />

          {/* Editor */}
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

          {/* Goals */}
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

      {/* Navigation */}
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

        {currentStep < tutorialSteps.length - 1 ? (
          <Button onClick={handleNextStep} className="gap-1">
            Next Step
            <ArrowRight className="h-4 w-4" />
          </Button>
        ) : (
          <Link href="/problems">
            <Button className="gap-1">
              Start Solving Problems
              <ArrowRight className="h-4 w-4" />
            </Button>
          </Link>
        )}
      </div>
    </div>
  );
}

/** Simple text formatter for bold (**) and code (`) */
function formatText(text: string): React.ReactNode {
  const parts: React.ReactNode[] = [];
  let remaining = text;
  let key = 0;

  while (remaining.length > 0) {
    // Check for bold
    const boldMatch = remaining.match(/\*\*(.+?)\*\*/);
    // Check for inline code
    const codeMatch = remaining.match(/`(.+?)`/);

    // Find earliest match
    const boldIdx = boldMatch ? remaining.indexOf(boldMatch[0]) : Infinity;
    const codeIdx = codeMatch ? remaining.indexOf(codeMatch[0]) : Infinity;

    if (boldIdx === Infinity && codeIdx === Infinity) {
      parts.push(remaining);
      break;
    }

    if (boldIdx <= codeIdx && boldMatch) {
      parts.push(remaining.slice(0, boldIdx));
      parts.push(<strong key={key++}>{boldMatch[1]}</strong>);
      remaining = remaining.slice(boldIdx + boldMatch[0].length);
    } else if (codeMatch) {
      parts.push(remaining.slice(0, codeIdx));
      parts.push(<code key={key++} className="bg-muted px-1 py-0.5 rounded text-xs font-mono">{codeMatch[1]}</code>);
      remaining = remaining.slice(codeIdx + codeMatch[0].length);
    }
  }

  return parts;
}
