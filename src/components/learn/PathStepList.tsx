'use client';

import Link from 'next/link';
import { CheckCircle2, Circle, ArrowRight } from 'lucide-react';
import { useProgressStore } from '@/store/progressStore';
import type { PathStep } from '@/lib/paths/types';

interface PathStepListProps {
  steps: PathStep[];
}

export function PathStepList({ steps }: PathStepListProps) {
  const { progress } = useProgressStore();

  return (
    <div className="space-y-0">
      {steps.map((step, index) => {
        const isCompleted = progress[step.problemSlug]?.completed;
        const isLast = index === steps.length - 1;

        return (
          <div key={step.problemSlug} className="flex gap-4">
            {/* Timeline */}
            <div className="flex flex-col items-center">
              {isCompleted ? (
                <CheckCircle2 className="h-6 w-6 text-green-500 shrink-0" />
              ) : (
                <Circle className="h-6 w-6 text-muted-foreground shrink-0" />
              )}
              {!isLast && (
                <div className={`w-0.5 flex-1 min-h-[24px] ${isCompleted ? 'bg-green-500' : 'bg-border'}`} />
              )}
            </div>

            {/* Content */}
            <div className="pb-6 flex-1">
              <Link
                href={`/problems/${step.problemSlug}`}
                className="group block"
              >
                <div className="flex items-center gap-2">
                  <span className={`font-medium group-hover:text-primary transition-colors ${isCompleted ? 'text-green-700 dark:text-green-400' : ''}`}>
                    {step.title}
                  </span>
                  <ArrowRight className="h-3 w-3 text-muted-foreground opacity-0 group-hover:opacity-100 transition-opacity" />
                </div>
                <p className="text-sm text-muted-foreground mt-0.5">{step.description}</p>
              </Link>
            </div>
          </div>
        );
      })}
    </div>
  );
}
