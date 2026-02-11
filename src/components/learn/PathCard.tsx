/**
 * @module PathCard
 *
 * Renders a single learning path as a clickable card with progress visualization.
 *
 * Each PathCard displays:
 *   - The path's icon, title, difficulty badge, and description
 *   - A progress bar showing how many steps the user has completed
 *   - A contextual footer: either "Completed" status, a "Continue" prompt
 *     pointing to the next unfinished step, or nothing if the path hasn't
 *     been started
 *
 * The progress computation is derived from the user's `progressStore` by
 * cross-referencing which problem slugs in the path's steps have been marked
 * as completed. This is done via `computePathProgress()` from the paths library.
 *
 * Design decisions:
 *   - The entire card is wrapped in a Next.js `<Link>` so the full surface
 *     area is clickable, improving mobile tap targets.
 *   - Difficulty badge colors come from a centralized `PATH_DIFFICULTY_COLORS`
 *     map in `ui-constants` to maintain visual consistency across the app.
 *   - The progress bar uses CSS `transition-all` for smooth width animations
 *     when progress changes (e.g., after completing a problem and returning
 *     to the Learn page).
 */
'use client';

import Link from 'next/link';
import { Card } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import { ArrowRight } from 'lucide-react';
import { useProgressStore } from '@/store/progressStore';
import { computePathProgress } from '@/lib/paths/progress';
import type { LearningPath } from '@/lib/paths/types';
import { PATH_DIFFICULTY_COLORS } from '@/lib/ui-constants';

/**
 * Props for the PathCard component.
 *
 * @property path - The learning path definition containing metadata (title,
 *   description, difficulty, icon) and an ordered array of steps.
 */
interface PathCardProps {
  path: LearningPath;
}

/**
 * Renders a learning path as an interactive card with progress tracking.
 *
 * Subscribes to `progressStore` to reactively update the progress bar
 * whenever the user completes a problem that belongs to this path.
 *
 * @param props - Component props containing the learning path data.
 * @returns A clickable card linking to the path's detail page.
 */
export function PathCard({ path }: PathCardProps) {
  /* Subscribe to the full progress record from the Zustand store.
     Using a selector for just `progress` (not the whole store) to minimize
     unnecessary re-renders -- only triggers when the progress map changes. */
  const progress = useProgressStore((s) => s.progress);

  /* Compute derived progress data: how many steps completed, next step index,
     and completion percentage. This is recalculated on every render but is
     cheap since it only iterates the path's steps array. */
  const pathProgress = computePathProgress(path, progress);

  /* Determine the next incomplete step to show in the "Continue" prompt.
     `nextStep` is null when all steps are complete. */
  const nextStep = pathProgress.nextStep !== null ? path.steps[pathProgress.nextStep] : null;
  const isComplete = pathProgress.completedSteps === pathProgress.totalSteps;

  return (
    <Link href={`/learn/${path.slug}`}>
      <Card className="p-4 h-full hover:bg-muted/50 transition-colors">
        <div className="flex items-start gap-3">
          {/* Path icon -- emoji character stored in the path definition */}
          <span className="text-2xl">{path.icon}</span>
          <div className="flex-1 min-w-0">
            {/* Title row with difficulty badge */}
            <div className="flex items-center gap-2 mb-1 flex-wrap">
              <h3 className="font-semibold">{path.title}</h3>
              {/* Difficulty badge uses color mapping from ui-constants for consistency */}
              <Badge className={PATH_DIFFICULTY_COLORS[path.difficulty]}>
                {path.difficulty}
              </Badge>
            </div>
            <p className="text-sm text-muted-foreground mb-3">{path.description}</p>

            {/* Progress bar -- visually represents completedSteps / totalSteps.
                The inner div's width is driven by the computed percentage with
                a smooth CSS transition for animated updates. */}
            <div className="flex items-center gap-2 mb-2">
              <div className="flex-1 h-1.5 bg-muted rounded-full overflow-hidden">
                <div
                  className="h-full bg-primary rounded-full transition-all duration-500"
                  style={{ width: `${pathProgress.percent}%` }}
                />
              </div>
              {/* Numeric progress indicator (e.g., "3/5") */}
              <span className="text-xs text-muted-foreground">
                {pathProgress.completedSteps}/{pathProgress.totalSteps}
              </span>
            </div>

            {/* Contextual footer: shows completion status or next step prompt.
                Three states: completed (green text), in-progress (continue link
                with arrow), or not started (renders nothing). */}
            {isComplete ? (
              <span className="text-xs text-green-600 dark:text-green-400 font-medium">Completed</span>
            ) : nextStep ? (
              <span className="text-xs text-primary inline-flex items-center gap-1">
                Continue: {nextStep.title}
                <ArrowRight className="h-3 w-3" />
              </span>
            ) : null}
          </div>
        </div>
      </Card>
    </Link>
  );
}
