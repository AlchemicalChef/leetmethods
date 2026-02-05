'use client';

import { ScrollArea } from '@/components/ui/scroll-area';
import { Separator } from '@/components/ui/separator';
import type { CoqGoal } from '@/lib/coq/types';

interface GoalsPanelProps {
  goals: CoqGoal[];
  isLoading?: boolean;
  isComplete?: boolean;
  className?: string;
}

export function GoalsPanel({ goals, isLoading, isComplete, className = '' }: GoalsPanelProps) {
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
        </div>
      </div>
    );
  }

  if (goals.length === 0) {
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
        <div className="text-sm text-muted-foreground">
          {goals.length} {goals.length === 1 ? 'goal' : 'goals'}
        </div>

        {goals.map((goal, index) => (
          <GoalDisplay key={goal.id} goal={goal} index={index} isFirst={index === 0} />
        ))}
      </div>
    </ScrollArea>
  );
}

interface GoalDisplayProps {
  goal: CoqGoal;
  index: number;
  isFirst: boolean;
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
