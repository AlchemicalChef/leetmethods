import type { ProblemProgress, StreakData } from '@/lib/types/progress';
import type { ProblemSummary, Category, Difficulty } from '@/lib/problems/types';

/**
 * Creates a ProblemProgress with sensible defaults.
 * Only specify the fields your test cares about.
 */
export function makeProgress(
  slug: string,
  completed: boolean,
  opts: Partial<Omit<ProblemProgress, 'slug' | 'completed'>> = {}
): ProblemProgress {
  return {
    slug,
    completed,
    completedAt: completed ? Date.now() : null,
    attempts: 1,
    hintsUsed: 0,
    solveStartedAt: null,
    solveDurationMs: null,
    srs: null,
    reviewAttempts: 0,
    reviewHintsUsed: 0,
    isReviewing: false,
    ...opts,
  };
}

/**
 * Creates a ProblemSummary with sensible defaults.
 */
export function makeProblem(
  slug: string,
  category: Category,
  difficulty: Difficulty = 'easy'
): ProblemSummary {
  return {
    id: slug,
    slug,
    title: slug.replace(/-/g, ' '),
    difficulty,
    category,
    tags: [],
  };
}

/** A zeroed-out streak for tests that don't care about streaks. */
export const NO_STREAK: StreakData = {
  currentStreak: 0,
  longestStreak: 0,
  lastSolveDate: null,
};
