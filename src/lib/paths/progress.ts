/**
 * Learning path progress computation.
 *
 * Calculates how far a user has progressed through a specific learning path
 * by cross-referencing the path's step list against the user's problem
 * completion records. This is used by the `/learn` page to display progress
 * bars and determine which step to highlight as "next".
 *
 * The progress computation is intentionally simple: a step is "completed"
 * if and only if the corresponding problem slug is marked as completed
 * in the progress store. There is no concept of "partial" completion
 * (started but not finished) at the path level.
 *
 * @module paths/progress
 */

import type { ProblemProgress } from '@/lib/types/progress';
import type { LearningPath } from './types';

/* ============================================================================
 * Type Definitions
 * ========================================================================= */

/**
 * Progress summary for a single learning path.
 *
 * @property completedSteps - Number of steps in the path that the user has completed.
 * @property totalSteps - Total number of steps in the path.
 * @property percent - Rounded completion percentage (0-100).
 * @property nextStep - Zero-based index of the first incomplete step, or `null`
 *                      if all steps are completed. This tells the UI which step
 *                      to highlight and link to.
 */
export interface PathProgress {
  completedSteps: number;
  totalSteps: number;
  percent: number;
  nextStep: number | null;
}

/* ============================================================================
 * Progress Computation
 * ========================================================================= */

/**
 * Computes the user's progress through a given learning path.
 *
 * Iterates through the path's steps in order, checking each step's problem
 * slug against the progress record. The first incomplete step is recorded
 * as `nextStep` to guide the user to where they should continue.
 *
 * Edge cases:
 * - If all steps are completed, `nextStep` is `null` (path is finished).
 * - If the path has no steps (empty `steps` array), returns 0% with `nextStep`
 *   as `null` (guard against division by zero).
 *
 * @param path - The learning path to evaluate progress for.
 * @param progress - The user's full progress record, keyed by problem slug.
 * @returns A `PathProgress` object summarizing the user's advancement through the path.
 */
export function computePathProgress(
  path: LearningPath,
  progress: Record<string, ProblemProgress>
): PathProgress {
  const totalSteps = path.steps.length;
  let completedSteps = 0;
  let nextStep: number | null = null;

  for (let i = 0; i < path.steps.length; i++) {
    if (progress[path.steps[i].problemSlug]?.completed) {
      completedSteps++;
    } else if (nextStep === null) {
      /**
       * Record the index of the first incomplete step. We only set this
       * once (when `nextStep` is still `null`) to get the earliest
       * incomplete step in the path's order.
       */
      nextStep = i;
    }
  }

  return {
    completedSteps,
    totalSteps,
    percent: totalSteps > 0 ? Math.round((completedSteps / totalSteps) * 100) : 0,
    /**
     * If the user has completed some steps but `nextStep` was never set
     * (all completed), return `null`. Otherwise, fall back to index 0
     * as a safety measure (should not happen in practice since
     * `completedSteps < totalSteps` implies at least one incomplete step
     * was found).
     */
    nextStep: completedSteps < totalSteps ? (nextStep ?? 0) : null,
  };
}
