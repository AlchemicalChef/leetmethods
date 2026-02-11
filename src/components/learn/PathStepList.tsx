/**
 * @module PathStepList
 *
 * Renders an ordered list of learning path steps as a vertical timeline.
 *
 * Each step is displayed with:
 *   - A timeline indicator (filled green check for completed, hollow circle
 *     for incomplete) connected by vertical lines
 *   - The step title and description, linked to the corresponding problem page
 *
 * This component is used on individual learning path detail pages to show
 * the full sequence of problems in the path and the user's progress through them.
 *
 * Design decisions:
 *   - The timeline uses a vertical connector line between steps that changes
 *     color based on completion status (green for completed, border color for
 *     incomplete), creating a visual "fill" effect as the user progresses.
 *   - The last step omits the connector line to avoid a dangling line below
 *     the final item.
 *   - Step titles have a hover effect (text-primary + arrow icon reveal) to
 *     indicate they are clickable links to problem pages.
 *   - The `shrink-0` class on icons prevents them from being compressed
 *     when step descriptions are long, maintaining timeline alignment.
 */
'use client';

import Link from 'next/link';
import { CheckCircle2, Circle, ArrowRight } from 'lucide-react';
import { useProgressStore } from '@/store/progressStore';
import type { PathStep } from '@/lib/paths/types';

/**
 * Props for the PathStepList component.
 *
 * @property steps - Ordered array of path steps, each containing a problem
 *   slug, title, and description. The order defines the recommended
 *   progression through the learning path.
 */
interface PathStepListProps {
  steps: PathStep[];
}

/**
 * Renders a vertical timeline of learning path steps with completion tracking.
 *
 * Subscribes to `progressStore` to reactively show which steps the user
 * has completed. Each step links to its corresponding problem page.
 *
 * @param props - Component props containing the ordered array of path steps.
 * @returns A vertical timeline UI showing step completion status.
 */
export function PathStepList({ steps }: PathStepListProps) {
  /* Subscribe to the progress record to determine which steps are completed.
     Each step's `problemSlug` is looked up in the progress map. */
  const progress = useProgressStore((s) => s.progress);

  return (
    <div className="space-y-0">
      {steps.map((step, index) => {
        /* Check if this step's associated problem has been completed */
        const isCompleted = progress[step.problemSlug]?.completed;
        /* Track whether this is the last step to conditionally hide the
           vertical connector line below it */
        const isLast = index === steps.length - 1;

        return (
          <div key={step.problemSlug} className="flex gap-4">
            {/* Timeline column -- contains the status icon and connecting line */}
            <div className="flex flex-col items-center">
              {/* Status icon: green filled check for completed, hollow circle for incomplete */}
              {isCompleted ? (
                <CheckCircle2 className="h-6 w-6 text-green-500 shrink-0" />
              ) : (
                <Circle className="h-6 w-6 text-muted-foreground shrink-0" />
              )}
              {/* Vertical connector line between steps.
                  Color reflects completion: green if the current step is done
                  (indicating progress "flow"), border color otherwise.
                  min-h ensures the line is visible even for short content. */}
              {!isLast && (
                <div className={`w-0.5 flex-1 min-h-[24px] ${isCompleted ? 'bg-green-500' : 'bg-border'}`} />
              )}
            </div>

            {/* Content column -- step title and description as a clickable link */}
            <div className="pb-6 flex-1">
              <Link
                href={`/problems/${step.problemSlug}`}
                className="group block"
              >
                <div className="flex items-center gap-2">
                  {/* Step title with hover color transition and green tint when completed */}
                  <span className={`font-medium group-hover:text-primary transition-colors ${isCompleted ? 'text-green-700 dark:text-green-400' : ''}`}>
                    {step.title}
                  </span>
                  {/* Arrow icon that fades in on hover to reinforce clickability */}
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
