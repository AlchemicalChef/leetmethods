import { describe, it, expect } from 'vitest';
import { computeStats, formatDuration } from './stats';
import type { ProblemProgress, StreakData } from '@/store/progressStore';
import type { ProblemSummary, Category, Difficulty } from '@/lib/problems/types';

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function makeProblem(
  slug: string,
  category: Category,
  difficulty: Difficulty
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

function makeProgress(
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
    ...opts,
  };
}

const NO_STREAK: StreakData = {
  currentStreak: 0,
  longestStreak: 0,
  lastSolveDate: null,
};

// ---------------------------------------------------------------------------
// computeStats
// ---------------------------------------------------------------------------

describe('computeStats', () => {
  it('returns all zeros for empty progress and empty problems', () => {
    const result = computeStats({}, [], NO_STREAK);

    expect(result.totalProblems).toBe(0);
    expect(result.solvedCount).toBe(0);
    expect(result.completionPercent).toBe(0);
    expect(result.currentStreak).toBe(0);
    expect(result.longestStreak).toBe(0);
    expect(result.totalTimeMs).toBe(0);
    expect(result.averageTimeMs).toBe(0);
    expect(result.categoryStats).toEqual([]);
    expect(result.difficultyStats).toEqual({
      easy: 0,
      medium: 0,
      hard: 0,
      easyTotal: 0,
      mediumTotal: 0,
      hardTotal: 0,
    });
    expect(result.totalAttempts).toBe(0);
    expect(result.totalHints).toBe(0);
  });

  it('computes solvedCount=1 and completionPercent=100 for a single completed problem', () => {
    const problems = [makeProblem('p1', 'logic', 'easy')];
    const progress = { p1: makeProgress('p1', true) };

    const result = computeStats(progress, problems, NO_STREAK);

    expect(result.totalProblems).toBe(1);
    expect(result.solvedCount).toBe(1);
    expect(result.completionPercent).toBe(100);
  });

  it('computes correct percentage for mixed completion (2 of 4 solved)', () => {
    const problems = [
      makeProblem('p1', 'logic', 'easy'),
      makeProblem('p2', 'logic', 'easy'),
      makeProblem('p3', 'lists', 'medium'),
      makeProblem('p4', 'lists', 'hard'),
    ];
    const progress: Record<string, ProblemProgress> = {
      p1: makeProgress('p1', true),
      p2: makeProgress('p2', false),
      p3: makeProgress('p3', true),
      p4: makeProgress('p4', false),
    };

    const result = computeStats(progress, problems, NO_STREAK);

    expect(result.solvedCount).toBe(2);
    expect(result.completionPercent).toBe(50);
  });

  it('produces category stats only for categories that have problems', () => {
    const problems = [
      makeProblem('p1', 'logic', 'easy'),
      makeProblem('p2', 'logic', 'easy'),
      makeProblem('p3', 'lists', 'medium'),
    ];
    const progress: Record<string, ProblemProgress> = {
      p1: makeProgress('p1', true),
      p2: makeProgress('p2', false),
      p3: makeProgress('p3', true),
    };

    const result = computeStats(progress, problems, NO_STREAK);

    // Only 'logic' and 'lists' should appear, in CATEGORY_ORDER order
    expect(result.categoryStats).toHaveLength(2);
    expect(result.categoryStats[0]).toEqual({
      category: 'logic',
      solved: 1,
      total: 2,
      percent: 50,
    });
    expect(result.categoryStats[1]).toEqual({
      category: 'lists',
      solved: 1,
      total: 1,
      percent: 100,
    });
  });

  it('excludes categories with 0 problems from categoryStats', () => {
    const problems = [makeProblem('p1', 'arithmetic', 'easy')];
    const progress = { p1: makeProgress('p1', true) };

    const result = computeStats(progress, problems, NO_STREAK);

    const categories = result.categoryStats.map((cs) => cs.category);
    expect(categories).toEqual(['arithmetic']);
    expect(categories).not.toContain('logic');
    expect(categories).not.toContain('induction');
    expect(categories).not.toContain('lists');
    expect(categories).not.toContain('data-structures');
    expect(categories).not.toContain('relations');
  });

  it('computes correct difficulty stats breakdown', () => {
    const problems = [
      makeProblem('e1', 'logic', 'easy'),
      makeProblem('e2', 'logic', 'easy'),
      makeProblem('m1', 'lists', 'medium'),
      makeProblem('h1', 'induction', 'hard'),
      makeProblem('h2', 'induction', 'hard'),
    ];
    const progress: Record<string, ProblemProgress> = {
      e1: makeProgress('e1', true),
      e2: makeProgress('e2', false),
      m1: makeProgress('m1', true),
      h1: makeProgress('h1', true),
      h2: makeProgress('h2', false),
    };

    const result = computeStats(progress, problems, NO_STREAK);

    expect(result.difficultyStats).toEqual({
      easy: 1,
      easyTotal: 2,
      medium: 1,
      mediumTotal: 1,
      hard: 1,
      hardTotal: 2,
    });
  });

  it('excludes null durations from averageTimeMs but accumulates totalTimeMs', () => {
    const problems = [
      makeProblem('p1', 'logic', 'easy'),
      makeProblem('p2', 'logic', 'easy'),
      makeProblem('p3', 'logic', 'easy'),
    ];
    const progress: Record<string, ProblemProgress> = {
      p1: makeProgress('p1', true, { solveDurationMs: 10000 }),
      p2: makeProgress('p2', true, { solveDurationMs: null }),
      p3: makeProgress('p3', true, { solveDurationMs: 30000 }),
    };

    const result = computeStats(progress, problems, NO_STREAK);

    expect(result.totalTimeMs).toBe(40000);
    // Average should only count the two timed solves (10000 + 30000) / 2
    expect(result.averageTimeMs).toBe(20000);
  });

  it('returns averageTimeMs=0 when no completed problems have duration', () => {
    const problems = [makeProblem('p1', 'logic', 'easy')];
    const progress = {
      p1: makeProgress('p1', true, { solveDurationMs: null }),
    };

    const result = computeStats(progress, problems, NO_STREAK);

    expect(result.totalTimeMs).toBe(0);
    expect(result.averageTimeMs).toBe(0);
  });

  it('passes through streak data from input', () => {
    const streak: StreakData = {
      currentStreak: 5,
      longestStreak: 12,
      lastSolveDate: '2025-01-15',
    };

    const result = computeStats({}, [], streak);

    expect(result.currentStreak).toBe(5);
    expect(result.longestStreak).toBe(12);
  });

  it('accumulates totalAttempts across all progress entries', () => {
    const problems = [
      makeProblem('p1', 'logic', 'easy'),
      makeProblem('p2', 'logic', 'easy'),
    ];
    const progress: Record<string, ProblemProgress> = {
      p1: makeProgress('p1', true, { attempts: 3 }),
      p2: makeProgress('p2', false, { attempts: 7 }),
    };

    const result = computeStats(progress, problems, NO_STREAK);

    expect(result.totalAttempts).toBe(10);
  });

  it('accumulates totalHints across all progress entries', () => {
    const problems = [
      makeProblem('p1', 'logic', 'easy'),
      makeProblem('p2', 'lists', 'medium'),
    ];
    const progress: Record<string, ProblemProgress> = {
      p1: makeProgress('p1', true, { hintsUsed: 2 }),
      p2: makeProgress('p2', false, { hintsUsed: 5 }),
    };

    const result = computeStats(progress, problems, NO_STREAK);

    expect(result.totalHints).toBe(7);
  });

  it('ignores incomplete problems when computing time stats', () => {
    const problems = [
      makeProblem('p1', 'logic', 'easy'),
      makeProblem('p2', 'logic', 'easy'),
    ];
    const progress: Record<string, ProblemProgress> = {
      p1: makeProgress('p1', true, { solveDurationMs: 5000 }),
      p2: makeProgress('p2', false, { solveDurationMs: 99999 }),
    };

    const result = computeStats(progress, problems, NO_STREAK);

    // Only p1 is completed, so only its duration counts
    expect(result.totalTimeMs).toBe(5000);
    expect(result.averageTimeMs).toBe(5000);
  });

  it('handles progress entries that have no matching problem', () => {
    // Progress exists for a slug not in the problems list
    const problems = [makeProblem('p1', 'logic', 'easy')];
    const progress: Record<string, ProblemProgress> = {
      p1: makeProgress('p1', true, { attempts: 1 }),
      orphan: makeProgress('orphan', true, { attempts: 2 }),
    };

    const result = computeStats(progress, problems, NO_STREAK);

    // solvedCount counts all completed in progress (including orphan)
    expect(result.solvedCount).toBe(2);
    // totalProblems is based on the problems list
    expect(result.totalProblems).toBe(1);
    // totalAttempts includes the orphan
    expect(result.totalAttempts).toBe(3);
  });

  it('preserves category order as defined in CATEGORY_ORDER', () => {
    // Provide problems in reverse order of CATEGORY_ORDER
    const problems = [
      makeProblem('r1', 'relations', 'easy'),
      makeProblem('d1', 'data-structures', 'easy'),
      makeProblem('a1', 'arithmetic', 'easy'),
      makeProblem('l1', 'lists', 'easy'),
      makeProblem('i1', 'induction', 'easy'),
      makeProblem('lo1', 'logic', 'easy'),
    ];

    const result = computeStats({}, problems, NO_STREAK);

    const order = result.categoryStats.map((cs) => cs.category);
    expect(order).toEqual([
      'logic',
      'induction',
      'lists',
      'arithmetic',
      'data-structures',
      'relations',
    ]);
  });
});

// ---------------------------------------------------------------------------
// formatDuration
// ---------------------------------------------------------------------------

describe('formatDuration', () => {
  it('returns "--" for 0ms', () => {
    expect(formatDuration(0)).toBe('--');
  });

  it('returns "1s" for 1000ms', () => {
    expect(formatDuration(1000)).toBe('1s');
  });

  it('returns "30s" for 30000ms', () => {
    expect(formatDuration(30000)).toBe('30s');
  });

  it('returns "1m 30s" for 90000ms', () => {
    expect(formatDuration(90000)).toBe('1m 30s');
  });

  it('returns "1m 0s" for exactly 60000ms', () => {
    expect(formatDuration(60000)).toBe('1m 0s');
  });

  it('returns "1h 0m" for exactly 3600000ms', () => {
    expect(formatDuration(3600000)).toBe('1h 0m');
  });

  it('returns "1h 1m" for 3660000ms', () => {
    expect(formatDuration(3660000)).toBe('1h 1m');
  });
});
