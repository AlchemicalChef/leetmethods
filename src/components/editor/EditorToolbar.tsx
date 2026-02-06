'use client';

import { Button } from '@/components/ui/button';
import { Play, StepForward, StepBack, RotateCcw, Check, Loader2, AlertCircle, HelpCircle } from 'lucide-react';
import type { CoqWorkerStatus } from '@/lib/coq/types';

interface EditorToolbarProps {
  status: CoqWorkerStatus;
  onExecuteNext: () => void;
  onExecutePrev: () => void;
  onExecuteAll: () => void;
  onReset: () => void;
  onSubmit: () => void;
  onShowShortcuts?: () => void;
  canSubmit?: boolean;
}

export function EditorToolbar({
  status,
  onExecuteNext,
  onExecutePrev,
  onExecuteAll,
  onReset,
  onSubmit,
  onShowShortcuts,
  canSubmit = true,
}: EditorToolbarProps) {
  const isReady = status === 'ready';
  const isBusy = status === 'busy' || status === 'loading';
  const isError = status === 'error';

  // FIX #15: Allow interaction on error state, reset can recover
  const canExecute = isReady;
  const canReset = !isBusy; // Allow reset even on error

  return (
    <div className="flex items-center justify-between px-3 py-2 border-b bg-muted/30">
      <div className="flex items-center gap-1">
        <StatusIndicator status={status} />

        <div className="w-px h-5 bg-border mx-2" />

        <Button
          variant="ghost"
          size="sm"
          onClick={onExecutePrev}
          disabled={!canExecute}
          title="Previous step (Alt+P or Alt+↑)"
        >
          <StepBack className="h-4 w-4" />
        </Button>

        <Button
          variant="ghost"
          size="sm"
          onClick={onExecuteNext}
          disabled={!canExecute}
          title="Next step (Alt+N or Alt+↓)"
        >
          <StepForward className="h-4 w-4" />
        </Button>

        <Button
          variant="ghost"
          size="sm"
          onClick={onExecuteAll}
          disabled={!canExecute}
          title="Execute all (Alt+Enter or Alt+→)"
        >
          <Play className="h-4 w-4" />
          <span className="ml-1 hidden sm:inline">Run</span>
        </Button>

        <Button
          variant="ghost"
          size="sm"
          onClick={onReset}
          disabled={!canReset}
          title={isError ? "Reset to recover from error" : "Reset execution"}
        >
          <RotateCcw className="h-4 w-4" />
        </Button>

        {/* FIX #15: Show error recovery hint */}
        {isError && (
          <span className="text-xs text-red-500 ml-2 hidden sm:inline">
            Click Reset to recover
          </span>
        )}

        {onShowShortcuts && (
          <>
            <div className="w-px h-5 bg-border mx-2" />
            <Button
              variant="ghost"
              size="sm"
              onClick={onShowShortcuts}
              title="Keyboard shortcuts (?)"
            >
              <HelpCircle className="h-4 w-4" />
            </Button>
          </>
        )}
      </div>

      <Button
        variant="default"
        size="sm"
        onClick={onSubmit}
        disabled={!canSubmit || isBusy}
        className="bg-green-600 hover:bg-green-700"
      >
        {isBusy ? (
          <Loader2 className="h-4 w-4 mr-1 animate-spin" />
        ) : isError ? (
          <AlertCircle className="h-4 w-4 mr-1" />
        ) : (
          <Check className="h-4 w-4 mr-1" />
        )}
        Submit
      </Button>
    </div>
  );
}

function StatusIndicator({ status }: { status: CoqWorkerStatus }) {
  const statusConfig: Record<CoqWorkerStatus, { color: string; label: string }> = {
    idle: { color: 'bg-gray-400', label: 'Idle' },
    loading: { color: 'bg-yellow-400 animate-pulse', label: 'Loading...' },
    ready: { color: 'bg-green-400', label: 'Ready' },
    busy: { color: 'bg-yellow-400 animate-pulse', label: 'Executing...' },
    error: { color: 'bg-red-400', label: 'Error' },
  };

  const { color, label } = statusConfig[status];

  return (
    <div className="flex items-center gap-2 text-sm text-muted-foreground">
      <div className={`w-2 h-2 rounded-full ${color}`} />
      <span className="hidden sm:inline">{label}</span>
    </div>
  );
}
