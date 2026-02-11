/**
 * @module EditorToolbar
 *
 * Toolbar component that provides execution controls for the Coq proof editor.
 *
 * This toolbar sits above the CoqEditor and provides buttons for:
 * - Step-by-step execution (forward/back) -- mirrors CoqIDE's proof navigation
 * - Execute all statements at once
 * - Execute to cursor position
 * - Reset execution state
 * - Submit proof for verification
 * - Toggle guided mode (tactic suggestions)
 * - Open keyboard shortcuts help
 *
 * The toolbar also shows a real-time status indicator (idle/loading/ready/busy/error)
 * that reflects the jsCoq worker state.
 *
 * Design decisions:
 * - Button enable/disable logic is carefully tied to the CoqWorkerStatus state
 *   machine. Execution requires 'ready' state, but reset is allowed even in
 *   'error' state to enable recovery (FIX #15).
 * - The submit button is a prominent green CTA separated to the right side
 *   to distinguish it from execution controls.
 * - Guided mode toggle uses amber coloring when active to indicate it's a
 *   learning aid, not a core execution control.
 * - Tooltips include keyboard shortcut hints for discoverability.
 *
 * @see {@link ProblemSolver} for the parent that provides callbacks
 * @see {@link CoqEditor} for the editor that handles the same keyboard shortcuts
 */
'use client';

import { Button } from '@/components/ui/button';
import { Play, StepForward, StepBack, RotateCcw, Check, Loader2, AlertCircle, HelpCircle, TextCursorInput, Lightbulb } from 'lucide-react';
import type { CoqWorkerStatus } from '@/lib/coq/types';

/* ============================================================================
 * Types
 * ============================================================================ */

/**
 * Props for the EditorToolbar component.
 */
interface EditorToolbarProps {
  /** Current status of the jsCoq worker (idle/loading/ready/busy/error) */
  status: CoqWorkerStatus;
  /** Execute the next Coq statement */
  onExecuteNext: () => void;
  /** Undo the last executed statement */
  onExecutePrev: () => void;
  /** Execute all remaining statements */
  onExecuteAll: () => void;
  /** Execute statements up to the current cursor position (optional feature) */
  onExecuteToCursor?: () => void;
  /** Reset Coq execution state and editor code */
  onReset: () => void;
  /** Submit the proof for full verification */
  onSubmit: () => void;
  /** Open the keyboard shortcuts help dialog */
  onShowShortcuts?: () => void;
  /** Whether the submit button should be enabled */
  canSubmit?: boolean;
  /** Whether guided mode (tactic suggestions) is currently active */
  guidedMode?: boolean;
  /** Toggle guided mode on/off */
  onToggleGuidedMode?: () => void;
}

/* ============================================================================
 * EditorToolbar Component
 * ============================================================================ */

/**
 * Toolbar with execution controls, status indicator, and submit button.
 *
 * @param props - See {@link EditorToolbarProps}
 * @returns The toolbar UI with execution controls on the left and submit on the right
 */
export function EditorToolbar({
  status,
  onExecuteNext,
  onExecutePrev,
  onExecuteAll,
  onExecuteToCursor,
  onReset,
  onSubmit,
  onShowShortcuts,
  canSubmit = true,
  guidedMode,
  onToggleGuidedMode,
}: EditorToolbarProps) {
  /** Coq is in a usable state where new commands can be sent */
  const isReady = status === 'ready';
  /** Coq is processing a command or still initializing */
  const isBusy = status === 'busy' || status === 'loading';
  /** Coq encountered an unrecoverable error */
  const isError = status === 'error';

  /**
   * FIX #15: Allow interaction on error state -- reset can recover the Coq
   * session. Execution requires 'ready', but reset only requires not-busy
   * so users can recover from error states without refreshing.
   */
  const canExecute = isReady;
  const canReset = !isBusy;

  return (
    <div className="flex items-center justify-between px-3 py-2 border-b bg-muted/30">
      {/* Left side: status indicator + execution controls */}
      <div className="flex items-center gap-1">
        <StatusIndicator status={status} />

        {/* Visual separator between status and controls */}
        <div className="w-px h-5 bg-border mx-2" />

        {/* Step backward -- undo the last executed Coq statement */}
        <Button
          variant="ghost"
          size="sm"
          onClick={onExecutePrev}
          disabled={!canExecute}
          title="Previous step (Alt+P or Alt+↑)"
          aria-label="Previous step"
        >
          <StepBack className="h-4 w-4" />
        </Button>

        {/* Step forward -- execute the next Coq statement */}
        <Button
          variant="ghost"
          size="sm"
          onClick={onExecuteNext}
          disabled={!canExecute}
          title="Next step (Alt+N or Alt+↓)"
          aria-label="Next step"
        >
          <StepForward className="h-4 w-4" />
        </Button>

        {/* Execute all -- run all remaining statements to completion */}
        <Button
          variant="ghost"
          size="sm"
          onClick={onExecuteAll}
          disabled={!canExecute}
          title="Execute all (Alt+Enter or Alt+→)"
          aria-label="Execute all"
        >
          <Play className="h-4 w-4" />
          <span className="ml-1 hidden sm:inline">Run</span>
        </Button>

        {/* Execute to cursor -- optional, only shown when handler is provided */}
        {onExecuteToCursor && (
          <Button
            variant="ghost"
            size="sm"
            onClick={onExecuteToCursor}
            disabled={!canExecute}
            title="Execute to cursor (Ctrl+Shift+Enter)"
            aria-label="Execute to cursor"
          >
            <TextCursorInput className="h-4 w-4" />
          </Button>
        )}

        {/* Reset -- clears Coq state and restores the problem template */}
        <Button
          variant="ghost"
          size="sm"
          onClick={onReset}
          disabled={!canReset}
          title={isError ? "Reset to recover from error" : "Reset execution"}
          aria-label="Reset"
        >
          <RotateCcw className="h-4 w-4" />
        </Button>

        {/* FIX #15: Show a recovery hint when Coq is in error state */}
        {isError && (
          <span className="text-xs text-red-500 ml-2 hidden sm:inline">
            Click Reset to recover
          </span>
        )}

        {/* Guided mode toggle -- shows/hides tactic suggestions in GoalsPanel */}
        {onToggleGuidedMode && (
          <>
            <div className="w-px h-5 bg-border mx-2" />
            <Button
              variant="ghost"
              size="sm"
              onClick={onToggleGuidedMode}
              title="Toggle guided suggestions"
              aria-label="Toggle guided suggestions"
              aria-pressed={guidedMode}
              className={guidedMode ? 'text-amber-500 hover:text-amber-600' : ''}
            >
              <Lightbulb className="h-4 w-4" />
            </Button>
          </>
        )}

        {/* Keyboard shortcuts help button */}
        {onShowShortcuts && (
          <>
            <div className="w-px h-5 bg-border mx-2" />
            <Button
              variant="ghost"
              size="sm"
              onClick={onShowShortcuts}
              title="Keyboard shortcuts (?)"
              aria-label="Keyboard shortcuts"
            >
              <HelpCircle className="h-4 w-4" />
            </Button>
          </>
        )}
      </div>

      {/* Right side: submit button -- the primary CTA */}
      <Button
        variant="default"
        size="sm"
        onClick={onSubmit}
        disabled={!canSubmit || isBusy}
        aria-label="Submit proof"
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

/* ============================================================================
 * StatusIndicator Sub-component
 * ============================================================================ */

/**
 * Small colored dot + label indicating the current jsCoq worker status.
 *
 * Status colors:
 * - **idle** (gray): Worker exists but no session started
 * - **loading** (yellow, pulsing): jsCoq is initializing (loading .vo files etc.)
 * - **ready** (green): Coq is ready to accept commands
 * - **busy** (yellow, pulsing): Coq is processing a statement
 * - **error** (red): Coq encountered an error
 *
 * The label text is hidden on small screens to save space, showing only the dot.
 *
 * @param props.status - Current CoqWorkerStatus value
 */
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
