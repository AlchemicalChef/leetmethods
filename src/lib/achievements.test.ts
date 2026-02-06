import { describe, it, expect } from 'vitest';
import { achievements, checkAchievements } from './achievements';
import type { ProblemProgress, StreakData } from '@/store/progressStore';
import type { ProblemSummary, Category, Difficulty } from '@/lib/problems/types';

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function makeProblem(
  slug: string,
  category: Category,
  difficulty: Difficulty = 'easy'
): ProblemSummary {
  return { id: slug, slug, title: slug, difficulty, category, tags: [] };
}

function makeProgress(
  slug: string,
  completed: boolean,
  opts?: Partial<Pick<ProblemProgress, 'attempts' | 'hintsUsed'>>
): ProblemProgress {
  return {
    slug,
    completed,
    completedAt: completed ? Date.now() : null,
    attempts: opts?.attempts ?? 1,
    hintsUsed: opts?.hintsUsed ?? 0,
    solveStartedAt: null,
    solveDurationMs: null,
  };
}

const defaultStreak: StreakData = {
  currentStreak: 0,
  longestStreak: 0,
  lastSolveDate: null,
};

// ---------------------------------------------------------------------------
// Achievements array sanity checks
// ---------------------------------------------------------------------------

describe('achievements array', () => {
  it('contains exactly 13 entries', () => {
    expect(achievements).toHaveLength(13);
  });

  it('every entry has id, title, description, icon, and category', () => {
    for (const a of achievements) {
      expect(a.id).toBeTruthy();
      expect(a.title).toBeTruthy();
      expect(a.description).toBeTruthy();
      expect(a.icon).toBeTruthy();
      expect(['milestone', 'mastery', 'skill', 'dedication']).toContain(a.category);
    }
  });
});

// ---------------------------------------------------------------------------
// checkAchievements
// ---------------------------------------------------------------------------

describe('checkAchievements', () => {
  // -- Empty / baseline -------------------------------------------------

  it('returns an empty array when progress is empty', () => {
    const result = checkAchievements({}, [makeProblem('p1', 'logic')], defaultStreak, new Set());
    expect(result).toEqual([]);
  });

  // -- Milestones -------------------------------------------------------

  it('unlocks first-proof when 1 problem is completed', () => {
    const progress: Record<string, ProblemProgress> = {
      p1: makeProgress('p1', true),
    };
    const problems = [makeProblem('p1', 'logic'), makeProblem('p2', 'logic')];
    const result = checkAchievements(progress, problems, defaultStreak, new Set());
    expect(result).toContain('first-proof');
  });

  it('does not unlock first-proof when no problems are completed', () => {
    const progress: Record<string, ProblemProgress> = {
      p1: makeProgress('p1', false),
    };
    const problems = [makeProblem('p1', 'logic')];
    const result = checkAchievements(progress, problems, defaultStreak, new Set());
    expect(result).not.toContain('first-proof');
  });

  it('unlocks five-proofs at 5 completions', () => {
    const progress: Record<string, ProblemProgress> = {};
    const problems: ProblemSummary[] = [];
    for (let i = 1; i <= 5; i++) {
      const slug = `p${i}`;
      progress[slug] = makeProgress(slug, true);
      problems.push(makeProblem(slug, 'logic'));
    }
    // Add extra problems so all-proofs does not trigger
    problems.push(makeProblem('p6', 'logic'));

    const result = checkAchievements(progress, problems, defaultStreak, new Set());
    expect(result).toContain('five-proofs');
    expect(result).not.toContain('ten-proofs');
  });

  it('unlocks ten-proofs at 10 completions', () => {
    const progress: Record<string, ProblemProgress> = {};
    const problems: ProblemSummary[] = [];
    for (let i = 1; i <= 10; i++) {
      const slug = `p${i}`;
      progress[slug] = makeProgress(slug, true);
      problems.push(makeProblem(slug, 'logic'));
    }
    // Extra problem to avoid all-proofs
    problems.push(makeProblem('p11', 'logic'));

    const result = checkAchievements(progress, problems, defaultStreak, new Set());
    expect(result).toContain('ten-proofs');
  });

  it('unlocks all-proofs when completedCount equals problems.length', () => {
    const problems = [makeProblem('a', 'logic'), makeProblem('b', 'induction')];
    const progress: Record<string, ProblemProgress> = {
      a: makeProgress('a', true),
      b: makeProgress('b', true),
    };
    const result = checkAchievements(progress, problems, defaultStreak, new Set());
    expect(result).toContain('all-proofs');
  });

  it('does not unlock all-proofs when problems.length is 0', () => {
    // Edge case: no problems in the list means the guard `problems.length > 0` prevents unlock
    const progress: Record<string, ProblemProgress> = {};
    const result = checkAchievements(progress, [], defaultStreak, new Set());
    expect(result).not.toContain('all-proofs');
  });

  // -- Category mastery -------------------------------------------------

  it('unlocks logic-master when all logic problems are completed', () => {
    const problems = [
      makeProblem('l1', 'logic'),
      makeProblem('l2', 'logic'),
      makeProblem('x1', 'induction'),
    ];
    const progress: Record<string, ProblemProgress> = {
      l1: makeProgress('l1', true),
      l2: makeProgress('l2', true),
    };
    const result = checkAchievements(progress, problems, defaultStreak, new Set());
    expect(result).toContain('logic-master');
    // Induction is not fully completed
    expect(result).not.toContain('induction-master');
  });

  it('does not unlock category mastery with partial completion', () => {
    const problems = [
      makeProblem('l1', 'logic'),
      makeProblem('l2', 'logic'),
    ];
    const progress: Record<string, ProblemProgress> = {
      l1: makeProgress('l1', true),
      // l2 not completed
    };
    const result = checkAchievements(progress, problems, defaultStreak, new Set());
    expect(result).not.toContain('logic-master');
  });

  it('does not unlock category mastery when category has no problems in the list', () => {
    // No 'relations' problems exist -> relations-master should not unlock
    const problems = [makeProblem('l1', 'logic')];
    const progress: Record<string, ProblemProgress> = {
      l1: makeProgress('l1', true),
    };
    const result = checkAchievements(progress, problems, defaultStreak, new Set());
    expect(result).not.toContain('relations-master');
  });

  // -- Skill achievements -----------------------------------------------

  it('unlocks no-hints when a completed problem has hintsUsed === 0', () => {
    const progress: Record<string, ProblemProgress> = {
      p1: makeProgress('p1', true, { hintsUsed: 0 }),
    };
    const result = checkAchievements(progress, [makeProblem('p1', 'logic')], defaultStreak, new Set());
    expect(result).toContain('no-hints');
  });

  it('does not unlock no-hints when all completed problems used hints', () => {
    const progress: Record<string, ProblemProgress> = {
      p1: makeProgress('p1', true, { hintsUsed: 2 }),
    };
    const result = checkAchievements(progress, [makeProblem('p1', 'logic')], defaultStreak, new Set());
    expect(result).not.toContain('no-hints');
  });

  it('unlocks first-try when a completed problem has attempts <= 1', () => {
    const progress: Record<string, ProblemProgress> = {
      p1: makeProgress('p1', true, { attempts: 1 }),
    };
    const result = checkAchievements(progress, [makeProblem('p1', 'logic')], defaultStreak, new Set());
    expect(result).toContain('first-try');
  });

  it('does not unlock first-try when all completed problems have attempts > 1', () => {
    const progress: Record<string, ProblemProgress> = {
      p1: makeProgress('p1', true, { attempts: 3 }),
    };
    const result = checkAchievements(progress, [makeProblem('p1', 'logic')], defaultStreak, new Set());
    expect(result).not.toContain('first-try');
  });

  it('unlocks persistence when a completed problem has attempts >= 10', () => {
    const progress: Record<string, ProblemProgress> = {
      p1: makeProgress('p1', true, { attempts: 10 }),
    };
    const result = checkAchievements(progress, [makeProblem('p1', 'logic')], defaultStreak, new Set());
    expect(result).toContain('persistence');
  });

  it('does not unlock persistence when max attempts is 9', () => {
    const progress: Record<string, ProblemProgress> = {
      p1: makeProgress('p1', true, { attempts: 9 }),
    };
    const result = checkAchievements(progress, [makeProblem('p1', 'logic')], defaultStreak, new Set());
    expect(result).not.toContain('persistence');
  });

  // -- Dedication -------------------------------------------------------

  it('unlocks streak-3 when currentStreak >= 3', () => {
    const streak: StreakData = { currentStreak: 3, longestStreak: 3, lastSolveDate: '2026-01-03' };
    const progress: Record<string, ProblemProgress> = {
      p1: makeProgress('p1', true),
    };
    const result = checkAchievements(progress, [makeProblem('p1', 'logic')], streak, new Set());
    expect(result).toContain('streak-3');
  });

  it('unlocks streak-3 when longestStreak >= 3 even if current is lower', () => {
    const streak: StreakData = { currentStreak: 1, longestStreak: 5, lastSolveDate: '2026-01-01' };
    const progress: Record<string, ProblemProgress> = {
      p1: makeProgress('p1', true),
    };
    const result = checkAchievements(progress, [makeProblem('p1', 'logic')], streak, new Set());
    expect(result).toContain('streak-3');
  });

  it('does not unlock streak-3 when both streaks are below 3', () => {
    const streak: StreakData = { currentStreak: 2, longestStreak: 2, lastSolveDate: '2026-01-01' };
    const progress: Record<string, ProblemProgress> = {
      p1: makeProgress('p1', true),
    };
    const result = checkAchievements(progress, [makeProblem('p1', 'logic')], streak, new Set());
    expect(result).not.toContain('streak-3');
  });

  // -- Already-unlocked filtering ---------------------------------------

  it('does not re-return already-unlocked achievement IDs', () => {
    const progress: Record<string, ProblemProgress> = {
      p1: makeProgress('p1', true),
    };
    const problems = [makeProblem('p1', 'logic')];
    const alreadyUnlocked = new Set(['first-proof', 'no-hints', 'first-try']);
    const result = checkAchievements(progress, problems, defaultStreak, alreadyUnlocked);
    expect(result).not.toContain('first-proof');
    expect(result).not.toContain('no-hints');
    expect(result).not.toContain('first-try');
  });

  // -- Multiple achievements at once ------------------------------------

  it('can unlock multiple achievements in a single call', () => {
    const problems = [makeProblem('p1', 'logic')];
    const progress: Record<string, ProblemProgress> = {
      p1: makeProgress('p1', true, { attempts: 1, hintsUsed: 0 }),
    };
    const streak: StreakData = { currentStreak: 3, longestStreak: 3, lastSolveDate: '2026-01-03' };
    const result = checkAchievements(progress, problems, streak, new Set());

    // Should unlock all of these simultaneously
    expect(result).toContain('first-proof');
    expect(result).toContain('all-proofs');
    expect(result).toContain('logic-master');
    expect(result).toContain('no-hints');
    expect(result).toContain('first-try');
    expect(result).toContain('streak-3');
    expect(result.length).toBeGreaterThanOrEqual(6);
  });

  // -- Incomplete progress is ignored for skill checks ------------------

  it('ignores incomplete problems for skill achievement checks', () => {
    // p1 is NOT completed but has hintsUsed 0 and attempts 1 -- should not count
    const progress: Record<string, ProblemProgress> = {
      p1: makeProgress('p1', false, { attempts: 1, hintsUsed: 0 }),
    };
    const result = checkAchievements(progress, [makeProblem('p1', 'logic')], defaultStreak, new Set());
    expect(result).not.toContain('no-hints');
    expect(result).not.toContain('first-try');
    expect(result).not.toContain('first-proof');
  });
});
