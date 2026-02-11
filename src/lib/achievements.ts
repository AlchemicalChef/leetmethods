/**
 * Achievement system for LeetMethods.
 *
 * Defines all unlockable achievements and provides the logic for checking whether
 * a user has earned new ones based on their current progress, problem completions,
 * streak data, and spaced repetition review history.
 *
 * Achievements are organized into four categories:
 * - **milestone**: Triggered by total proof completion counts (1, 5, 10, all).
 * - **mastery**: Triggered by completing every problem within a specific Coq category.
 * - **skill**: Triggered by demonstrating proficiency (no hints, first try, persistence).
 * - **dedication**: Triggered by sustained engagement (streaks, spaced reviews).
 *
 * This module is a pure function library with no side effects. The `achievementStore`
 * (Zustand) is responsible for persisting which achievements have been unlocked and
 * surfacing toast notifications. This module only computes which achievements are
 * newly earned given the current state.
 *
 * @module achievements
 */

import type { ProblemProgress, StreakData } from '@/lib/types/progress';
import type { ProblemSummary, Category } from '@/lib/problems/types';

/* ============================================================================
 * Type Definitions
 * ========================================================================= */

/**
 * Represents a single achievement that a user can unlock.
 *
 * @property id - Unique identifier used as the key in the unlocked set and for persistence.
 * @property title - Human-readable name shown in the achievements UI.
 * @property description - Short explanation of what the user must do to earn this achievement.
 * @property icon - Emoji string used as the visual icon in the UI.
 * @property category - Grouping category for display and filtering purposes.
 */
export interface Achievement {
  id: string;
  title: string;
  description: string;
  icon: string;
  category: 'milestone' | 'mastery' | 'skill' | 'dedication';
}

/* ============================================================================
 * Achievement Definitions
 * ========================================================================= */

/**
 * The complete list of all achievements available in the application.
 *
 * New achievements should be added here and will automatically be checked
 * by `checkAchievements()`. The `id` must be unique and stable across
 * releases, since it is persisted in localStorage via the achievement store.
 */
export const achievements: Achievement[] = [
  /* -- Milestone achievements: based on total completed proof count -- */
  { id: 'first-proof', title: 'First Proof', description: 'Complete your first proof', icon: '🎯', category: 'milestone' },
  { id: 'five-proofs', title: 'Getting Started', description: 'Complete 5 proofs', icon: '🌱', category: 'milestone' },
  { id: 'ten-proofs', title: 'Double Digits', description: 'Complete 10 proofs', icon: '🔟', category: 'milestone' },
  { id: 'all-proofs', title: 'Completionist', description: 'Complete all problems', icon: '🏆', category: 'milestone' },

  /* -- Mastery achievements: one per problem category, earned by completing all problems in that category -- */
  { id: 'logic-master', title: 'Logic Master', description: 'Complete all Logic problems', icon: '🧠', category: 'mastery' },
  { id: 'induction-master', title: 'Induction Expert', description: 'Complete all Induction problems', icon: '🔄', category: 'mastery' },
  { id: 'list-master', title: 'List Wrangler', description: 'Complete all List problems', icon: '📋', category: 'mastery' },
  { id: 'data-structures-master', title: 'Tree Climber', description: 'Complete all Data Structures problems', icon: '🌳', category: 'mastery' },
  { id: 'arithmetic-master', title: 'Number Cruncher', description: 'Complete all Arithmetic problems', icon: '🔢', category: 'mastery' },
  { id: 'relations-master', title: 'Relation Builder', description: 'Complete all Relations problems', icon: '🔗', category: 'mastery' },

  /* -- Skill achievements: based on how the user solves problems -- */
  { id: 'no-hints', title: 'No Hints Needed', description: 'Complete a problem without using any hints', icon: '💡', category: 'skill' },
  { id: 'first-try', title: 'First Try', description: 'Complete a problem on the first attempt', icon: '⚡', category: 'skill' },
  { id: 'persistence', title: 'Persistence', description: 'Complete a problem after 10+ attempts', icon: '💪', category: 'skill' },

  /* -- Dedication achievements: based on sustained engagement over time -- */
  { id: 'streak-3', title: 'Hat Trick', description: 'Maintain a 3-day solve streak', icon: '🔥', category: 'dedication' },
  { id: 'first-review', title: 'First Review', description: 'Complete your first spaced review', icon: '🔄', category: 'dedication' },
  { id: 'ten-reviews', title: 'Review Master', description: 'Complete 10 spaced reviews', icon: '📚', category: 'dedication' },
  { id: 'perfect-recall', title: 'Perfect Recall', description: 'Complete a review on the first attempt with no hints', icon: '🧠', category: 'skill' },
];

/* ============================================================================
 * Category Mastery Mapping
 * ========================================================================= */

/**
 * Maps each category-mastery achievement ID to its corresponding problem `Category`.
 *
 * This allows `checkAchievements()` to iterate over mastery achievements generically
 * rather than hard-coding category checks individually.
 */
const categoryMap: Record<string, Category> = {
  'logic-master': 'logic',
  'induction-master': 'induction',
  'list-master': 'lists',
  'arithmetic-master': 'arithmetic',
  'data-structures-master': 'data-structures',
  'relations-master': 'relations',
};

/* ============================================================================
 * Achievement Checking Logic
 * ========================================================================= */

/**
 * Evaluates the user's current progress and returns the IDs of any newly unlocked achievements.
 *
 * This function is idempotent and side-effect-free: it compares the current state against
 * the set of already-unlocked achievement IDs and returns only those that are newly earned.
 * The caller (typically the achievement store) is responsible for persisting the results
 * and displaying toast notifications.
 *
 * Design note: Completions are filtered to only count known (non-custom, non-orphaned)
 * problem slugs. This prevents deleted or custom problems from inflating milestone counts
 * (referred to as the "H8 fix" in earlier development).
 *
 * @param progress - The full progress record keyed by problem slug.
 * @param problems - The list of all known (built-in) problem summaries.
 * @param streakData - The user's current and longest streak information.
 * @param unlockedIds - The set of achievement IDs the user has already unlocked.
 * @returns An array of achievement IDs that were newly unlocked during this check.
 */
export function checkAchievements(
  progress: Record<string, ProblemProgress>,
  problems: ProblemSummary[],
  streakData: StreakData,
  unlockedIds: Set<string>
): string[] {
  const newlyUnlocked: string[] = [];

  /**
   * Build a set of known problem slugs so we only count completions for
   * problems that still exist in the problem registry. This excludes
   * custom problems and any orphaned progress entries from removed problems.
   */
  const knownSlugs = new Set(problems.map((p) => p.slug));
  const completed = Object.values(progress).filter((p) => p.completed && knownSlugs.has(p.slug));
  const completedCount = completed.length;

  /**
   * Helper that conditionally adds an achievement ID to `newlyUnlocked`
   * if the condition is met and the achievement is not already unlocked.
   *
   * @param id - The achievement ID to check.
   * @param condition - Whether the achievement's criteria are satisfied.
   */
  const check = (id: string, condition: boolean) => {
    if (!unlockedIds.has(id) && condition) {
      newlyUnlocked.push(id);
    }
  };

  /* -- Milestone checks: based on total completion count -- */
  check('first-proof', completedCount >= 1);
  check('five-proofs', completedCount >= 5);
  check('ten-proofs', completedCount >= 10);
  check('all-proofs', completedCount >= problems.length && problems.length > 0);

  /* -- Category mastery checks: all problems in a category must be completed -- */
  for (const [achId, category] of Object.entries(categoryMap)) {
    const categoryProblems = problems.filter((p) => p.category === category);
    if (categoryProblems.length > 0) {
      const allCompleted = categoryProblems.every((p) => progress[p.slug]?.completed);
      check(achId, allCompleted);
    }
  }

  /* -- Skill checks: based on individual problem solve quality -- */
  check('no-hints', completed.some((p) => p.hintsUsed === 0));
  check('first-try', completed.some((p) => p.attempts <= 1));
  check('persistence', completed.some((p) => p.attempts >= 10));

  /* -- Dedication checks: based on streak data -- */
  check('streak-3', streakData.longestStreak >= 3 || streakData.currentStreak >= 3);

  /* -- SRS (Spaced Repetition) achievement checks -- */
  const allProgress = Object.values(progress);
  let totalReviewCount = 0;
  let hasPerfectRecall = false;
  for (const p of allProgress) {
    if (p.srs) {
      totalReviewCount += p.srs.reviewCount;
      /**
       * A "perfect recall" requires at least one completed review with the
       * highest quality score (5), meaning the user solved it on the first
       * attempt with no hints during a spaced review session.
       */
      if (p.srs.reviewCount > 0 && p.srs.lastReviewQuality >= 5) {
        hasPerfectRecall = true;
      }
    }
  }
  check('first-review', totalReviewCount >= 1);
  check('ten-reviews', totalReviewCount >= 10);
  check('perfect-recall', hasPerfectRecall);

  return newlyUnlocked;
}
