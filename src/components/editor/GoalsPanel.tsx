/**
 * @module GoalsPanel
 *
 * Displays Coq proof state -- goals, hypotheses, and messages -- in a panel
 * alongside the CoqEditor.
 *
 * This component mirrors the "Goals" window found in CoqIDE and other Coq IDEs.
 * It shows the user what they still need to prove (the goal conclusion), what
 * assumptions are available (hypotheses), and any messages from the Coq engine
 * (errors, warnings, success notices).
 *
 * The panel has four distinct visual states:
 * 1. **Loading** -- spinner while Coq is executing
 * 2. **Complete** -- success message with optional "next problem" link
 * 3. **Empty** -- prompt to execute code
 * 4. **Active** -- shows messages, goals, and optional guided suggestions
 *
 * Design decisions:
 * - Only the 5 most recent messages are shown to avoid overwhelming the user
 *   while still providing enough context for debugging.
 * - Error messages are passed through `formatCoqError()` which provides
 *   user-friendly explanations alongside the raw Coq error (expandable).
 * - The first goal is visually distinguished (primary border/color) since
 *   it is the one the user should focus on -- subsequent goals are subgoals.
 * - Guided suggestions are rendered via GuidedProofPanel when guided mode is on.
 *
 * @see {@link ProblemSolver} for the parent that provides goals/messages state
 * @see {@link GuidedProofPanel} for tactic suggestion display
 */
'use client';

import { useState } from 'react';
import { AlertCircle, AlertTriangle, ArrowRight, CheckCircle2, ChevronDown, ChevronRight, Info } from 'lucide-react';
import { ScrollArea } from '@/components/ui/scroll-area';
import { Separator } from '@/components/ui/separator';
import type { CoqGoal } from '@/lib/coq/types';
import type { CoqMessage } from '@/store/coqStore';
import type { ProblemSummary } from '@/lib/problems/types';
import type { TacticSuggestion } from '@/lib/coq/tactic-suggester';
import { formatCoqError } from '@/lib/coq/error-helper';
import { getTypeBadge } from '@/lib/coq/type-classifier';
import { GuidedProofPanel } from './GuidedProofPanel';
import Link from 'next/link';

/* ============================================================================
 * GoalsPanel Component
 * ============================================================================ */

/**
 * Props for the GoalsPanel component.
 */
interface GoalsPanelProps {
  /** Array of current Coq proof goals (hypotheses + conclusion per goal) */
  goals: CoqGoal[];
  /** Recent Coq messages (errors, warnings, info, success) */
  messages?: CoqMessage[];
  /** Whether Coq is currently executing a statement */
  isLoading?: boolean;
  /** Whether the proof has been fully completed (no remaining goals after submit) */
  isComplete?: boolean;
  /** The next recommended problem to solve after completion */
  nextProblem?: ProblemSummary | null;
  /** Tactic suggestions from the guided proof system */
  guidedSuggestions?: TacticSuggestion[];
  /** Callback to insert a tactic at the editor cursor position */
  onInsertTactic?: (tactic: string) => void;
  /** Additional CSS classes for the container */
  className?: string;
}

/**
 * Panel displaying Coq proof goals, hypotheses, messages, and guided suggestions.
 *
 * Renders different UIs based on the current state: loading spinner, completion
 * celebration, empty prompt, or the full goals + messages view.
 *
 * @param props - See {@link GoalsPanelProps}
 * @returns The goals panel UI
 */
export function GoalsPanel({ goals, messages = [], isLoading, isComplete, nextProblem, guidedSuggestions, onInsertTactic, className = '' }: GoalsPanelProps) {
  /* --- Loading state: show spinner while Coq is executing --- */
  if (isLoading) {
    return (
      <div className={`flex items-center justify-center h-full bg-muted/30 ${className}`}>
        <div className="flex items-center gap-2 text-muted-foreground">
          <div className="animate-spin rounded-full h-4 w-4 border-2 border-primary border-t-transparent" />
          <span>Executing...</span>
        </div>
      </div>
    );
  }

  /* --- Complete state: proof is done, show success and optional next problem --- */
  if (isComplete) {
    return (
      <div className={`flex items-center justify-center h-full bg-green-50 dark:bg-green-950/20 ${className}`}>
        <div className="text-center">
          <div className="text-2xl mb-2">✓</div>
          <div className="text-green-700 dark:text-green-400 font-medium">No more goals</div>
          <div className="text-sm text-muted-foreground mt-1">Proof complete!</div>
          {nextProblem && (
            <Link
              href={nextProblem.isCustom ? `/problems/custom/${nextProblem.slug}` : `/problems/${nextProblem.slug}`}
              className="inline-flex items-center gap-1 text-sm text-primary hover:underline mt-3"
            >
              Next: {nextProblem.title}
              <ArrowRight className="h-3 w-3" />
            </Link>
          )}
        </div>
      </div>
    );
  }

  /**
   * Show only the 5 most recent messages to keep the panel focused.
   * Older messages scroll off -- the full history is in coqStore.messages
   * (capped at 100 entries).
   */
  const recentMessages = messages.slice(-5);

  /* --- Empty state: no goals or messages yet --- */
  if (goals.length === 0 && recentMessages.length === 0) {
    return (
      <div className={`flex items-center justify-center h-full bg-muted/30 ${className}`}>
        <div className="text-muted-foreground text-sm">
          Execute code to see proof goals
        </div>
      </div>
    );
  }

  /* --- Active state: show messages, goals, and optionally guided suggestions --- */
  return (
    <ScrollArea className={`h-full ${className}`}>
      <div className="p-4 space-y-4">
        {/* Messages section -- errors, warnings, success notices */}
        {recentMessages.length > 0 && (
          <div className="space-y-2">
            {recentMessages.map((msg, i) => (
              <MessageDisplay key={`${msg.timestamp}-${i}`} message={msg} />
            ))}
          </div>
        )}

        {/* Goals section -- each goal shows hypotheses and conclusion */}
        {goals.length > 0 && (
          <>
            <div className="text-sm text-muted-foreground">
              {goals.length} {goals.length === 1 ? 'goal' : 'goals'}
            </div>
            {goals.map((goal, index) => (
              <GoalDisplay key={goal.id} goal={goal} index={index} isFirst={index === 0} />
            ))}
          </>
        )}

        {/* Guided suggestions -- shown when guided mode is enabled and goals exist */}
        {guidedSuggestions && guidedSuggestions.length > 0 && (
          <GuidedProofPanel suggestions={guidedSuggestions} onInsertTactic={onInsertTactic} />
        )}
      </div>
    </ScrollArea>
  );
}

/* ============================================================================
 * Message Display Components
 * ============================================================================ */

/**
 * Props for the GoalDisplay sub-component.
 */
interface GoalDisplayProps {
  /** The Coq goal object containing hypotheses and conclusion */
  goal: CoqGoal;
  /** Zero-based index of this goal in the goals array */
  index: number;
  /** Whether this is the first (primary/focused) goal */
  isFirst: boolean;
}

/**
 * Visual style configuration for each message type.
 * Maps message types to their icon component, background, border, text,
 * and icon colors for both light and dark themes.
 */
const messageStyles = {
  error: { icon: AlertCircle, bg: 'bg-red-50 dark:bg-red-950/30', border: 'border-red-200 dark:border-red-900', text: 'text-red-700 dark:text-red-400', iconColor: 'text-red-500' },
  warning: { icon: AlertTriangle, bg: 'bg-yellow-50 dark:bg-yellow-950/30', border: 'border-yellow-200 dark:border-yellow-900', text: 'text-yellow-700 dark:text-yellow-400', iconColor: 'text-yellow-500' },
  success: { icon: CheckCircle2, bg: 'bg-green-50 dark:bg-green-950/30', border: 'border-green-200 dark:border-green-900', text: 'text-green-700 dark:text-green-400', iconColor: 'text-green-500' },
  info: { icon: Info, bg: 'bg-blue-50 dark:bg-blue-950/30', border: 'border-blue-200 dark:border-blue-900', text: 'text-blue-700 dark:text-blue-400', iconColor: 'text-blue-500' },
  notice: { icon: Info, bg: 'bg-muted/50', border: 'border-border', text: 'text-muted-foreground', iconColor: 'text-muted-foreground' },
} as const;

/**
 * Renders a single Coq message with appropriate styling based on type.
 *
 * For error messages, attempts to provide a user-friendly explanation via
 * `formatCoqError()`. If a friendly message is available, renders the
 * expandable FriendlyErrorDisplay instead.
 *
 * @param props.message - The Coq message to display
 */
function MessageDisplay({ message }: { message: CoqMessage }) {
  const style = messageStyles[message.type] || messageStyles.info;
  const Icon = style.icon;

  // For errors, try to provide a friendlier explanation with expandable raw details
  if (message.type === 'error') {
    const { friendly, raw } = formatCoqError(message.content);
    if (friendly) {
      return <FriendlyErrorDisplay friendly={friendly} raw={raw} style={style} />;
    }
  }

  return (
    <div className={`flex items-start gap-2 px-3 py-2 rounded-md border text-sm ${style.bg} ${style.border} ${style.text}`}>
      <Icon className={`h-4 w-4 mt-0.5 shrink-0 ${style.iconColor}`} />
      <span className="break-words min-w-0">{message.content}</span>
    </div>
  );
}

/**
 * Expandable error display that shows a human-readable explanation at the top
 * and allows the user to expand to see the raw Coq error output.
 *
 * This two-level approach helps beginners understand what went wrong while
 * still giving advanced users access to the full error for debugging.
 *
 * @param props.friendly - The user-friendly error explanation
 * @param props.raw - The raw Coq error message
 * @param props.style - Visual style configuration from messageStyles
 */
function FriendlyErrorDisplay({ friendly, raw, style }: { friendly: string; raw: string; style: (typeof messageStyles)[keyof typeof messageStyles] }) {
  const [expanded, setExpanded] = useState(false);
  const Icon = style.icon;
  return (
    <div className={`px-3 py-2 rounded-md border text-sm ${style.bg} ${style.border} ${style.text}`}>
      <div className="flex items-start gap-2">
        <Icon className={`h-4 w-4 mt-0.5 shrink-0 ${style.iconColor}`} />
        <span className="break-words min-w-0">{friendly}</span>
      </div>
      <button
        onClick={() => setExpanded(!expanded)}
        className="flex items-center gap-1 mt-1.5 ml-6 text-xs opacity-70 hover:opacity-100 transition-opacity"
      >
        {expanded ? <ChevronDown className="h-3 w-3" /> : <ChevronRight className="h-3 w-3" />}
        Raw error
      </button>
      {expanded && (
        <pre className="mt-1 ml-6 text-xs opacity-70 whitespace-pre-wrap break-words font-mono">{raw}</pre>
      )}
    </div>
  );
}

/* ============================================================================
 * Goal Display Component
 * ============================================================================ */

/**
 * Renders a single Coq proof goal, showing its hypotheses (assumptions in scope)
 * and the conclusion (what needs to be proved).
 *
 * The first goal receives primary styling (highlighted border and text) since
 * it is the active goal the user should focus on. Subsequent goals are subgoals
 * that will become active after the current goal is solved.
 *
 * Layout follows the standard Coq convention:
 * ```
 *   H1 : nat
 *   H2 : H1 > 0
 *   ────────────
 *   H1 + 1 > 1
 * ```
 *
 * @param props - See {@link GoalDisplayProps}
 */
function GoalDisplay({ goal, index, isFirst }: GoalDisplayProps) {
  return (
    <div
      className={`rounded-lg border ${
        isFirst ? 'border-primary bg-primary/5' : 'border-border bg-muted/20'
      }`}
    >
      {/* Goal header with 1-based index */}
      <div className="px-3 py-2 border-b bg-muted/50 text-xs font-medium text-muted-foreground">
        Goal {index + 1}
      </div>

      <div className="p-3 space-y-3">
        {/* Hypotheses -- named assumptions available in the proof context */}
        {goal.hypotheses.length > 0 && (
          <div className="space-y-1">
            {goal.hypotheses.map((hyp, hypIndex) => {
              const badge = getTypeBadge(hyp.type);
              return (
                <div key={hypIndex} className="font-mono text-sm flex items-baseline gap-2">
                  <span className="text-blue-600 dark:text-blue-400 font-medium min-w-[60px]">
                    {hyp.name}
                  </span>
                  <span className="text-muted-foreground">:</span>
                  <span className="text-foreground">{hyp.type}</span>
                  {badge && (
                    <span
                      className={`inline-flex items-center px-1.5 py-0 rounded text-[10px] font-medium leading-4 shrink-0 ${badge.className}`}
                      title={badge.title}
                    >
                      {badge.label}
                    </span>
                  )}
                </div>
              );
            })}
          </div>
        )}

        {/* Separator line between hypotheses and conclusion (the "turnstile") */}
        {goal.hypotheses.length > 0 && (
          <Separator className="my-2" />
        )}

        {/* Conclusion -- the proposition that needs to be proved */}
        <div className="font-mono text-sm flex items-baseline gap-2">
          <span className={isFirst ? 'text-primary font-medium' : 'text-foreground'}>
            {goal.conclusion}
          </span>
          {(() => {
            const badge = getTypeBadge(goal.conclusion);
            return badge ? (
              <span
                className={`inline-flex items-center px-1.5 py-0 rounded text-[10px] font-medium leading-4 shrink-0 ${badge.className}`}
                title={badge.title}
              >
                {badge.label}
              </span>
            ) : null;
          })()}
        </div>
      </div>
    </div>
  );
}
