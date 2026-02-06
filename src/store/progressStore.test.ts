import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { updateStreak, getDateString, useProgressStore } from './progressStore';
import type { StreakData } from './progressStore';

// ---------------------------------------------------------------------------
// getDateString
// ---------------------------------------------------------------------------

describe('getDateString', () => {
  it('returns a string in YYYY-MM-DD format', () => {
    // 2025-06-15 at noon local time
    const ts = new Date(2025, 5, 15, 12, 0, 0).getTime();
    expect(getDateString(ts)).toBe('2025-06-15');
  });

  it('zero-pads single-digit months', () => {
    // March = month index 2 → should produce "03"
    const ts = new Date(2025, 2, 20, 10, 0, 0).getTime();
    expect(getDateString(ts)).toBe('2025-03-20');
  });

  it('zero-pads single-digit days', () => {
    // 2025-11-05
    const ts = new Date(2025, 10, 5, 8, 0, 0).getTime();
    expect(getDateString(ts)).toBe('2025-11-05');
  });

  it('handles January 1 correctly (year boundary)', () => {
    const ts = new Date(2026, 0, 1, 0, 0, 0).getTime();
    expect(getDateString(ts)).toBe('2026-01-01');
  });

  it('handles December 31 correctly', () => {
    const ts = new Date(2025, 11, 31, 23, 59, 59).getTime();
    expect(getDateString(ts)).toBe('2025-12-31');
  });

  it('produces consistent output at midnight vs noon for the same day', () => {
    const midnight = new Date(2025, 7, 10, 0, 0, 0).getTime();
    const noon = new Date(2025, 7, 10, 12, 0, 0).getTime();
    expect(getDateString(midnight)).toBe(getDateString(noon));
    expect(getDateString(midnight)).toBe('2025-08-10');
  });

  it('handles double-digit months and days without extra padding', () => {
    // 2025-12-25
    const ts = new Date(2025, 11, 25, 15, 30, 0).getTime();
    expect(getDateString(ts)).toBe('2025-12-25');
  });
});

// ---------------------------------------------------------------------------
// updateStreak
// ---------------------------------------------------------------------------

describe('updateStreak', () => {
  beforeEach(() => {
    vi.useFakeTimers();
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  it('starts a new streak of 1 when lastSolveDate is null (first solve)', () => {
    vi.setSystemTime(new Date(2025, 5, 15, 12, 0, 0)); // 2025-06-15

    const input: StreakData = {
      currentStreak: 0,
      longestStreak: 0,
      lastSolveDate: null,
    };

    const result = updateStreak(input);

    expect(result.currentStreak).toBe(1);
    expect(result.longestStreak).toBe(1);
    expect(result.lastSolveDate).toBe('2025-06-15');
  });

  it('returns the same object when already solved today (no change)', () => {
    vi.setSystemTime(new Date(2025, 5, 15, 14, 0, 0)); // 2025-06-15

    const input: StreakData = {
      currentStreak: 3,
      longestStreak: 5,
      lastSolveDate: '2025-06-15',
    };

    const result = updateStreak(input);

    // Should return the exact same reference
    expect(result).toBe(input);
    expect(result.currentStreak).toBe(3);
    expect(result.longestStreak).toBe(5);
    expect(result.lastSolveDate).toBe('2025-06-15');
  });

  it('increments streak by 1 when solving on a consecutive day', () => {
    vi.setSystemTime(new Date(2025, 5, 16, 10, 0, 0)); // 2025-06-16

    const input: StreakData = {
      currentStreak: 3,
      longestStreak: 5,
      lastSolveDate: '2025-06-15', // yesterday
    };

    const result = updateStreak(input);

    expect(result.currentStreak).toBe(4);
    expect(result.longestStreak).toBe(5); // still 5, since 4 < 5
    expect(result.lastSolveDate).toBe('2025-06-16');
  });

  it('resets streak to 1 when there is a gap of more than 1 day', () => {
    vi.setSystemTime(new Date(2025, 5, 20, 10, 0, 0)); // 2025-06-20

    const input: StreakData = {
      currentStreak: 7,
      longestStreak: 10,
      lastSolveDate: '2025-06-15', // 5 days ago
    };

    const result = updateStreak(input);

    expect(result.currentStreak).toBe(1);
    expect(result.longestStreak).toBe(10); // preserved
    expect(result.lastSolveDate).toBe('2025-06-20');
  });

  it('does not decrease longestStreak when current streak resets', () => {
    vi.setSystemTime(new Date(2025, 5, 20, 10, 0, 0)); // 2025-06-20

    const input: StreakData = {
      currentStreak: 3,
      longestStreak: 15,
      lastSolveDate: '2025-06-10', // 10 days ago
    };

    const result = updateStreak(input);

    expect(result.currentStreak).toBe(1);
    expect(result.longestStreak).toBe(15);
  });

  it('updates longestStreak when current streak exceeds it', () => {
    vi.setSystemTime(new Date(2025, 5, 16, 10, 0, 0)); // 2025-06-16

    const input: StreakData = {
      currentStreak: 5,
      longestStreak: 5,
      lastSolveDate: '2025-06-15', // yesterday
    };

    const result = updateStreak(input);

    expect(result.currentStreak).toBe(6);
    expect(result.longestStreak).toBe(6); // updated to new max
  });

  it('resets streak to 1 when gap is exactly 2 days', () => {
    vi.setSystemTime(new Date(2025, 5, 17, 10, 0, 0)); // 2025-06-17

    const input: StreakData = {
      currentStreak: 4,
      longestStreak: 4,
      lastSolveDate: '2025-06-15', // 2 days ago
    };

    const result = updateStreak(input);

    expect(result.currentStreak).toBe(1);
    expect(result.longestStreak).toBe(4); // preserved
    expect(result.lastSolveDate).toBe('2025-06-17');
  });

  it('handles consecutive solves across a month boundary', () => {
    vi.setSystemTime(new Date(2025, 7, 1, 10, 0, 0)); // 2025-08-01

    const input: StreakData = {
      currentStreak: 2,
      longestStreak: 2,
      lastSolveDate: '2025-07-31', // yesterday, crossing month boundary
    };

    const result = updateStreak(input);

    expect(result.currentStreak).toBe(3);
    expect(result.longestStreak).toBe(3);
    expect(result.lastSolveDate).toBe('2025-08-01');
  });

  it('handles consecutive solves across a year boundary', () => {
    vi.setSystemTime(new Date(2026, 0, 1, 10, 0, 0)); // 2026-01-01

    const input: StreakData = {
      currentStreak: 10,
      longestStreak: 10,
      lastSolveDate: '2025-12-31', // yesterday, crossing year boundary
    };

    const result = updateStreak(input);

    expect(result.currentStreak).toBe(11);
    expect(result.longestStreak).toBe(11);
    expect(result.lastSolveDate).toBe('2026-01-01');
  });

  it('simulates multiple consecutive days of solves', () => {
    // Day 1: first solve
    vi.setSystemTime(new Date(2025, 5, 10, 12, 0, 0)); // 2025-06-10
    let streak: StreakData = {
      currentStreak: 0,
      longestStreak: 0,
      lastSolveDate: null,
    };

    streak = updateStreak(streak);
    expect(streak.currentStreak).toBe(1);
    expect(streak.longestStreak).toBe(1);
    expect(streak.lastSolveDate).toBe('2025-06-10');

    // Day 2: consecutive
    vi.setSystemTime(new Date(2025, 5, 11, 9, 0, 0)); // 2025-06-11
    streak = updateStreak(streak);
    expect(streak.currentStreak).toBe(2);
    expect(streak.longestStreak).toBe(2);

    // Day 3: consecutive
    vi.setSystemTime(new Date(2025, 5, 12, 18, 0, 0)); // 2025-06-12
    streak = updateStreak(streak);
    expect(streak.currentStreak).toBe(3);
    expect(streak.longestStreak).toBe(3);

    // Day 4: skip a day (gap)
    vi.setSystemTime(new Date(2025, 5, 14, 10, 0, 0)); // 2025-06-14
    streak = updateStreak(streak);
    expect(streak.currentStreak).toBe(1); // reset
    expect(streak.longestStreak).toBe(3); // preserved from earlier run

    // Day 5: consecutive again
    vi.setSystemTime(new Date(2025, 5, 15, 10, 0, 0)); // 2025-06-15
    streak = updateStreak(streak);
    expect(streak.currentStreak).toBe(2);
    expect(streak.longestStreak).toBe(3); // still 3
  });

  it('calling updateStreak twice on the same day only counts once', () => {
    vi.setSystemTime(new Date(2025, 5, 15, 8, 0, 0)); // morning

    let streak: StreakData = {
      currentStreak: 0,
      longestStreak: 0,
      lastSolveDate: null,
    };

    streak = updateStreak(streak);
    expect(streak.currentStreak).toBe(1);

    // Call again in the afternoon of the same day
    vi.setSystemTime(new Date(2025, 5, 15, 20, 0, 0)); // evening
    const secondResult = updateStreak(streak);

    // Should be the exact same reference (no-op)
    expect(secondResult).toBe(streak);
    expect(secondResult.currentStreak).toBe(1);
  });
});

// ---------------------------------------------------------------------------
// Zustand store actions
// ---------------------------------------------------------------------------

describe('useProgressStore - getProgress', () => {
  beforeEach(() => {
    useProgressStore.setState({
      progress: {},
      streakData: { currentStreak: 0, longestStreak: 0, lastSolveDate: null },
    });
  });

  it('returns undefined for unknown slug', () => {
    const result = useProgressStore.getState().getProgress('unknown-problem');
    expect(result).toBeUndefined();
  });

  it('returns entry after mutation', () => {
    const { incrementAttempts, getProgress } = useProgressStore.getState();
    incrementAttempts('two-sum');
    const result = getProgress('two-sum');
    expect(result).toBeDefined();
    expect(result?.slug).toBe('two-sum');
    expect(result?.attempts).toBe(1);
  });
});

describe('useProgressStore - incrementAttempts', () => {
  beforeEach(() => {
    useProgressStore.setState({
      progress: {},
      streakData: { currentStreak: 0, longestStreak: 0, lastSolveDate: null },
    });
  });

  it('creates default entry and increments', () => {
    const { incrementAttempts } = useProgressStore.getState();
    incrementAttempts('two-sum');
    const progress = useProgressStore.getState().progress['two-sum'];
    expect(progress).toBeDefined();
    expect(progress.slug).toBe('two-sum');
    expect(progress.attempts).toBe(1);
    expect(progress.completed).toBe(false);
    expect(progress.hintsUsed).toBe(0);
  });

  it('increments existing entry', () => {
    useProgressStore.setState({
      progress: {
        'two-sum': {
          slug: 'two-sum',
          completed: false,
          completedAt: null,
          attempts: 3,
          hintsUsed: 1,
          solveStartedAt: null,
          solveDurationMs: null,
        },
      },
      streakData: { currentStreak: 0, longestStreak: 0, lastSolveDate: null },
    });
    const { incrementAttempts } = useProgressStore.getState();
    incrementAttempts('two-sum');
    const progress = useProgressStore.getState().progress['two-sum'];
    expect(progress.attempts).toBe(4);
    expect(progress.hintsUsed).toBe(1);
  });

  it('multiple increments accumulate', () => {
    const { incrementAttempts } = useProgressStore.getState();
    incrementAttempts('problem-1');
    incrementAttempts('problem-1');
    incrementAttempts('problem-1');
    const progress = useProgressStore.getState().progress['problem-1'];
    expect(progress.attempts).toBe(3);
  });
});

describe('useProgressStore - incrementHints', () => {
  beforeEach(() => {
    useProgressStore.setState({
      progress: {},
      streakData: { currentStreak: 0, longestStreak: 0, lastSolveDate: null },
    });
  });

  it('creates default and increments', () => {
    const { incrementHints } = useProgressStore.getState();
    incrementHints('two-sum');
    const progress = useProgressStore.getState().progress['two-sum'];
    expect(progress).toBeDefined();
    expect(progress.slug).toBe('two-sum');
    expect(progress.hintsUsed).toBe(1);
    expect(progress.completed).toBe(false);
    expect(progress.attempts).toBe(0);
  });

  it('increments existing', () => {
    useProgressStore.setState({
      progress: {
        'two-sum': {
          slug: 'two-sum',
          completed: false,
          completedAt: null,
          attempts: 2,
          hintsUsed: 1,
          solveStartedAt: null,
          solveDurationMs: null,
        },
      },
      streakData: { currentStreak: 0, longestStreak: 0, lastSolveDate: null },
    });
    const { incrementHints } = useProgressStore.getState();
    incrementHints('two-sum');
    const progress = useProgressStore.getState().progress['two-sum'];
    expect(progress.hintsUsed).toBe(2);
    expect(progress.attempts).toBe(2);
  });

  it('multiple increments', () => {
    const { incrementHints } = useProgressStore.getState();
    incrementHints('problem-1');
    incrementHints('problem-1');
    const progress = useProgressStore.getState().progress['problem-1'];
    expect(progress.hintsUsed).toBe(2);
  });
});

describe('useProgressStore - markCompleted', () => {
  beforeEach(() => {
    vi.useFakeTimers();
    useProgressStore.setState({
      progress: {},
      streakData: { currentStreak: 0, longestStreak: 0, lastSolveDate: null },
    });
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  it('marks slug completed with timestamp', () => {
    vi.setSystemTime(new Date('2024-01-15T12:00:00Z'));
    const { markCompleted } = useProgressStore.getState();
    markCompleted('two-sum');
    const progress = useProgressStore.getState().progress['two-sum'];
    expect(progress.completed).toBe(true);
    expect(progress.completedAt).toBe(new Date('2024-01-15T12:00:00Z').getTime());
  });

  it('stops running timer and calculates duration', () => {
    vi.setSystemTime(new Date('2024-01-15T12:00:00Z'));
    const { startTimer, markCompleted } = useProgressStore.getState();
    startTimer('two-sum');
    vi.setSystemTime(new Date('2024-01-15T12:05:00Z'));
    markCompleted('two-sum');
    const progress = useProgressStore.getState().progress['two-sum'];
    expect(progress.completed).toBe(true);
    expect(progress.solveStartedAt).toBe(null);
    expect(progress.solveDurationMs).toBe(5 * 60 * 1000);
  });

  it('updates streak data', () => {
    vi.setSystemTime(new Date('2024-01-15T12:00:00Z'));
    useProgressStore.setState({
      progress: {},
      streakData: { currentStreak: 2, longestStreak: 5, lastSolveDate: '2024-01-14' },
    });
    const { markCompleted } = useProgressStore.getState();
    markCompleted('two-sum');
    const streakData = useProgressStore.getState().streakData;
    expect(streakData.currentStreak).toBe(3);
    expect(streakData.lastSolveDate).toBe('2024-01-15');
  });

  it("doesn't re-increment attempts", () => {
    useProgressStore.setState({
      progress: {
        'two-sum': {
          slug: 'two-sum',
          completed: false,
          completedAt: null,
          attempts: 5,
          hintsUsed: 2,
          solveStartedAt: null,
          solveDurationMs: null,
        },
      },
      streakData: { currentStreak: 0, longestStreak: 0, lastSolveDate: null },
    });
    const { markCompleted } = useProgressStore.getState();
    markCompleted('two-sum');
    const progress = useProgressStore.getState().progress['two-sum'];
    expect(progress.attempts).toBe(5);
    expect(progress.hintsUsed).toBe(2);
  });
});

describe('useProgressStore - startTimer', () => {
  beforeEach(() => {
    vi.useFakeTimers();
    useProgressStore.setState({
      progress: {},
      streakData: { currentStreak: 0, longestStreak: 0, lastSolveDate: null },
    });
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  it('sets solveStartedAt', () => {
    vi.setSystemTime(new Date('2024-01-15T12:00:00Z'));
    const { startTimer } = useProgressStore.getState();
    startTimer('two-sum');
    const progress = useProgressStore.getState().progress['two-sum'];
    expect(progress.solveStartedAt).toBe(new Date('2024-01-15T12:00:00Z').getTime());
    expect(progress.solveDurationMs).toBe(null);
  });

  it('no-op if already running', () => {
    vi.setSystemTime(new Date('2024-01-15T12:00:00Z'));
    const { startTimer } = useProgressStore.getState();
    startTimer('two-sum');
    const firstStart = useProgressStore.getState().progress['two-sum'].solveStartedAt;
    vi.setSystemTime(new Date('2024-01-15T12:05:00Z'));
    startTimer('two-sum');
    const secondStart = useProgressStore.getState().progress['two-sum'].solveStartedAt;
    expect(firstStart).toBe(secondStart);
  });

  it('no-op if completed', () => {
    useProgressStore.setState({
      progress: {
        'two-sum': {
          slug: 'two-sum',
          completed: true,
          completedAt: Date.now(),
          attempts: 1,
          hintsUsed: 0,
          solveStartedAt: null,
          solveDurationMs: 1000,
        },
      },
      streakData: { currentStreak: 0, longestStreak: 0, lastSolveDate: null },
    });
    const { startTimer } = useProgressStore.getState();
    startTimer('two-sum');
    const progress = useProgressStore.getState().progress['two-sum'];
    expect(progress.solveStartedAt).toBe(null);
  });
});

describe('useProgressStore - stopTimer', () => {
  beforeEach(() => {
    vi.useFakeTimers();
    useProgressStore.setState({
      progress: {},
      streakData: { currentStreak: 0, longestStreak: 0, lastSolveDate: null },
    });
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  it('calculates elapsed time', () => {
    vi.setSystemTime(new Date('2024-01-15T12:00:00Z'));
    const { startTimer, stopTimer } = useProgressStore.getState();
    startTimer('two-sum');
    vi.setSystemTime(new Date('2024-01-15T12:03:00Z'));
    stopTimer('two-sum');
    const progress = useProgressStore.getState().progress['two-sum'];
    expect(progress.solveStartedAt).toBe(null);
    expect(progress.solveDurationMs).toBe(3 * 60 * 1000);
  });

  it('accumulates with existing duration', () => {
    vi.setSystemTime(new Date('2024-01-15T12:00:00Z'));
    useProgressStore.setState({
      progress: {
        'two-sum': {
          slug: 'two-sum',
          completed: false,
          completedAt: null,
          attempts: 0,
          hintsUsed: 0,
          solveStartedAt: new Date('2024-01-15T12:00:00Z').getTime(),
          solveDurationMs: 2000,
        },
      },
      streakData: { currentStreak: 0, longestStreak: 0, lastSolveDate: null },
    });
    vi.setSystemTime(new Date('2024-01-15T12:01:00Z'));
    const { stopTimer } = useProgressStore.getState();
    stopTimer('two-sum');
    const progress = useProgressStore.getState().progress['two-sum'];
    expect(progress.solveDurationMs).toBe(2000 + 60 * 1000);
  });

  it('no-op when no timer running', () => {
    const { stopTimer } = useProgressStore.getState();
    stopTimer('two-sum');
    const progress = useProgressStore.getState().progress['two-sum'];
    expect(progress).toBeUndefined();
  });
});

describe('useProgressStore - getCompletedCount / getCompletedSlugs', () => {
  beforeEach(() => {
    useProgressStore.setState({
      progress: {},
      streakData: { currentStreak: 0, longestStreak: 0, lastSolveDate: null },
    });
  });

  it('returns 0/empty initially', () => {
    const { getCompletedCount, getCompletedSlugs } = useProgressStore.getState();
    expect(getCompletedCount()).toBe(0);
    expect(getCompletedSlugs()).toEqual([]);
  });

  it('counts completed entries', () => {
    useProgressStore.setState({
      progress: {
        'problem-1': {
          slug: 'problem-1',
          completed: true,
          completedAt: Date.now(),
          attempts: 1,
          hintsUsed: 0,
          solveStartedAt: null,
          solveDurationMs: 1000,
        },
        'problem-2': {
          slug: 'problem-2',
          completed: false,
          completedAt: null,
          attempts: 2,
          hintsUsed: 1,
          solveStartedAt: null,
          solveDurationMs: null,
        },
        'problem-3': {
          slug: 'problem-3',
          completed: true,
          completedAt: Date.now(),
          attempts: 1,
          hintsUsed: 0,
          solveStartedAt: null,
          solveDurationMs: 2000,
        },
      },
      streakData: { currentStreak: 0, longestStreak: 0, lastSolveDate: null },
    });
    const { getCompletedCount } = useProgressStore.getState();
    expect(getCompletedCount()).toBe(2);
  });

  it('returns slugs of completed entries', () => {
    useProgressStore.setState({
      progress: {
        'problem-1': {
          slug: 'problem-1',
          completed: true,
          completedAt: Date.now(),
          attempts: 1,
          hintsUsed: 0,
          solveStartedAt: null,
          solveDurationMs: 1000,
        },
        'problem-2': {
          slug: 'problem-2',
          completed: false,
          completedAt: null,
          attempts: 2,
          hintsUsed: 1,
          solveStartedAt: null,
          solveDurationMs: null,
        },
        'problem-3': {
          slug: 'problem-3',
          completed: true,
          completedAt: Date.now(),
          attempts: 1,
          hintsUsed: 0,
          solveStartedAt: null,
          solveDurationMs: 2000,
        },
      },
      streakData: { currentStreak: 0, longestStreak: 0, lastSolveDate: null },
    });
    const { getCompletedSlugs } = useProgressStore.getState();
    const slugs = getCompletedSlugs();
    expect(slugs).toHaveLength(2);
    expect(slugs).toContain('problem-1');
    expect(slugs).toContain('problem-3');
  });
});
