/**
 * Problem recommendation engine for LeetMethods.
 *
 * After a user completes a problem, this module suggests the next problem they
 * should attempt. The recommendation follows a priority-based strategy that
 * balances two goals:
 *
 * 1. **Reinforcement**: Stay within the same category and difficulty to build mastery.
 * 2. **Progression**: Gradually increase difficulty, then branch to new categories.
 *
 * The priority order is:
 *   0. Due spaced repetition reviews (highest priority, to maintain recall)
 *   1. Same category, same difficulty (reinforce current skill level)
 *   2. Same category, next harder difficulty (progress within category)
 *   3. Any unsolved in same category (complete the category)
 *   4. Same difficulty, any category (branch out at comfortable level)
 *   5. Easiest unsolved overall (fallback)
 *
 * This module is a pure function with no side effects. It relies on the caller
 * (typically the ProblemSolver component) to provide the current problem context,
 * the full problem list, and the user's completion state.
 *
 * @module recommendations
 */

import type { ProblemSummary } from '@/lib/problems/types';
import { DIFFICULTY_ORDER } from '@/lib/ui-constants';

/**
 * Determines the next problem to recommend after the user finishes the current one.
 *
 * The algorithm filters out already-completed problems and the current problem,
 * then applies the priority cascade described in the module documentation.
 * If all problems are completed, returns `null`.
 *
 * @param currentProblem - The problem the user just completed or is currently viewing.
 * @param allProblems - The full list of available problem summaries.
 * @param completedSlugs - Array of slugs the user has already completed.
 * @param dueSlugs - Optional array of slugs that are due for spaced repetition review.
 *                   These take highest priority to ensure the user doesn't fall behind
 *                   on their review schedule.
 * @returns The recommended next problem, or `null` if no unsolved problems remain.
 */
export function getNextRecommendation(
  currentProblem: ProblemSummary,
  allProblems: ProblemSummary[],
  completedSlugs: string[],
  dueSlugs?: string[]
): ProblemSummary | null {
  /**
   * Priority 0: If there are problems due for spaced repetition review,
   * recommend the first one (excluding the current problem). Reviews take
   * precedence because delaying them degrades long-term retention.
   */
  if (dueSlugs && dueSlugs.length > 0) {
    const dueReview = allProblems.find((p) => dueSlugs.includes(p.slug) && p.slug !== currentProblem.slug);
    if (dueReview) return dueReview;
  }

  const completed = new Set(completedSlugs);
  const unsolved = allProblems.filter((p) => !completed.has(p.slug) && p.slug !== currentProblem.slug);

  if (unsolved.length === 0) return null;

  /**
   * Priority 1: Same category and same difficulty level.
   * This keeps the user practicing similar problems to build confidence
   * before moving on to harder ones.
   */
  const sameCatSameDiff = unsolved.filter(
    (p) => p.category === currentProblem.category && p.difficulty === currentProblem.difficulty
  );
  if (sameCatSameDiff.length > 0) return sameCatSameDiff[0];

  /**
   * Priority 2: Same category, next harder difficulty.
   * Sorted by difficulty order so the user gets the gentlest step up.
   * Uses DIFFICULTY_ORDER numeric mapping (easy=0, medium=1, hard=2) for comparison.
   */
  const sameCatHarder = unsolved
    .filter(
      (p) =>
        p.category === currentProblem.category &&
        DIFFICULTY_ORDER[p.difficulty] > DIFFICULTY_ORDER[currentProblem.difficulty]
    )
    .sort((a, b) => DIFFICULTY_ORDER[a.difficulty] - DIFFICULTY_ORDER[b.difficulty]);
  if (sameCatHarder.length > 0) return sameCatHarder[0];

  /**
   * Priority 3: Any unsolved problem in the same category, regardless of difficulty.
   * This handles the case where easier problems remain in the same category.
   */
  const sameCat = unsolved.filter((p) => p.category === currentProblem.category);
  if (sameCat.length > 0) return sameCat[0];

  /**
   * Priority 4: Same difficulty level in any category.
   * Encourages breadth by exploring new categories at a comfortable difficulty.
   */
  const sameDiff = unsolved.filter((p) => p.difficulty === currentProblem.difficulty);
  if (sameDiff.length > 0) return sameDiff[0];

  /**
   * Priority 5 (fallback): Return the easiest unsolved problem across all categories.
   * Ensures the user always has a recommendation, even if nothing else matches.
   */
  return unsolved.sort((a, b) => DIFFICULTY_ORDER[a.difficulty] - DIFFICULTY_ORDER[b.difficulty])[0];
}
