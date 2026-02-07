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
import { GuidedProofPanel } from './GuidedProofPanel';
import Link from 'next/link';

interface GoalsPanelProps {
  goals: CoqGoal[];
  messages?: CoqMessage[];
  isLoading?: boolean;
  isComplete?: boolean;
  nextProblem?: ProblemSummary | null;
  guidedSuggestions?: TacticSuggestion[];
  className?: string;
}

export function GoalsPanel({ goals, messages = [], isLoading, isComplete, nextProblem, guidedSuggestions, className = '' }: GoalsPanelProps) {
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

  if (isComplete) {
    return (
      <div className={`flex items-center justify-center h-full bg-green-50 dark:bg-green-950/20 ${className}`}>
        <div className="text-center">
          <div className="text-2xl mb-2">✓</div>
          <div className="text-green-700 dark:text-green-400 font-medium">No more goals</div>
          <div className="text-sm text-muted-foreground mt-1">Proof complete!</div>
          {nextProblem && (
            <Link
              href={`/problems/${nextProblem.slug}`}
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

  // Show recent messages (last 5) relevant to current state
  const recentMessages = messages.slice(-5);

  if (goals.length === 0 && recentMessages.length === 0) {
    return (
      <div className={`flex items-center justify-center h-full bg-muted/30 ${className}`}>
        <div className="text-muted-foreground text-sm">
          Execute code to see proof goals
        </div>
      </div>
    );
  }

  return (
    <ScrollArea className={`h-full ${className}`}>
      <div className="p-4 space-y-4">
        {/* Messages */}
        {recentMessages.length > 0 && (
          <div className="space-y-2">
            {recentMessages.map((msg, i) => (
              <MessageDisplay key={`${msg.timestamp}-${i}`} message={msg} />
            ))}
          </div>
        )}

        {/* Goals */}
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

        {/* Guided suggestions */}
        {guidedSuggestions && guidedSuggestions.length > 0 && (
          <GuidedProofPanel suggestions={guidedSuggestions} />
        )}
      </div>
    </ScrollArea>
  );
}

interface GoalDisplayProps {
  goal: CoqGoal;
  index: number;
  isFirst: boolean;
}

const messageStyles = {
  error: { icon: AlertCircle, bg: 'bg-red-50 dark:bg-red-950/30', border: 'border-red-200 dark:border-red-900', text: 'text-red-700 dark:text-red-400', iconColor: 'text-red-500' },
  warning: { icon: AlertTriangle, bg: 'bg-yellow-50 dark:bg-yellow-950/30', border: 'border-yellow-200 dark:border-yellow-900', text: 'text-yellow-700 dark:text-yellow-400', iconColor: 'text-yellow-500' },
  success: { icon: CheckCircle2, bg: 'bg-green-50 dark:bg-green-950/30', border: 'border-green-200 dark:border-green-900', text: 'text-green-700 dark:text-green-400', iconColor: 'text-green-500' },
  info: { icon: Info, bg: 'bg-blue-50 dark:bg-blue-950/30', border: 'border-blue-200 dark:border-blue-900', text: 'text-blue-700 dark:text-blue-400', iconColor: 'text-blue-500' },
  notice: { icon: Info, bg: 'bg-muted/50', border: 'border-border', text: 'text-muted-foreground', iconColor: 'text-muted-foreground' },
} as const;

function MessageDisplay({ message }: { message: CoqMessage }) {
  const style = messageStyles[message.type] || messageStyles.info;
  const Icon = style.icon;

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

function GoalDisplay({ goal, index, isFirst }: GoalDisplayProps) {
  return (
    <div
      className={`rounded-lg border ${
        isFirst ? 'border-primary bg-primary/5' : 'border-border bg-muted/20'
      }`}
    >
      <div className="px-3 py-2 border-b bg-muted/50 text-xs font-medium text-muted-foreground">
        Goal {index + 1}
      </div>

      <div className="p-3 space-y-3">
        {/* Hypotheses */}
        {goal.hypotheses.length > 0 && (
          <div className="space-y-1">
            {goal.hypotheses.map((hyp, hypIndex) => (
              <div key={hypIndex} className="font-mono text-sm flex gap-2">
                <span className="text-blue-600 dark:text-blue-400 font-medium min-w-[60px]">
                  {hyp.name}
                </span>
                <span className="text-muted-foreground">:</span>
                <span className="text-foreground">{hyp.type}</span>
              </div>
            ))}
          </div>
        )}

        {/* Separator */}
        {goal.hypotheses.length > 0 && (
          <Separator className="my-2" />
        )}

        {/* Conclusion */}
        <div className="font-mono text-sm">
          <span className={isFirst ? 'text-primary font-medium' : 'text-foreground'}>
            {goal.conclusion}
          </span>
        </div>
      </div>
    </div>
  );
}
