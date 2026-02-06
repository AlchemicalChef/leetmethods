import { describe, it, expect } from 'vitest';
import {
  getAllProblems,
  getProblemBySlug,
  getProblemSummaries,
  getProblemsByCategory,
  getProblemsByDifficulty,
} from './loader';

// ---------------------------------------------------------------------------
// getAllProblems
// ---------------------------------------------------------------------------

describe('getAllProblems', () => {
  it('returns an array of problems', async () => {
    const problems = await getAllProblems();
    expect(Array.isArray(problems)).toBe(true);
    expect(problems.length).toBeGreaterThan(0);
  });

  it('every problem has all required fields', async () => {
    const problems = await getAllProblems();
    for (const p of problems) {
      expect(p.id).toBeTruthy();
      expect(p.slug).toBeTruthy();
      expect(p.title).toBeTruthy();
      expect(['easy', 'medium', 'hard']).toContain(p.difficulty);
      expect(['logic', 'induction', 'lists', 'arithmetic', 'data-structures', 'relations']).toContain(p.category);
      expect(Array.isArray(p.tags)).toBe(true);
      expect(typeof p.description).toBe('string');
      expect(Array.isArray(p.hints)).toBe(true);
      expect(typeof p.prelude).toBe('string');
      expect(typeof p.template).toBe('string');
      expect(typeof p.solution).toBe('string');
      expect(Array.isArray(p.forbiddenTactics)).toBe(true);
    }
  });

  it('has unique slugs across all problems', async () => {
    const problems = await getAllProblems();
    const slugs = problems.map((p) => p.slug);
    expect(new Set(slugs).size).toBe(slugs.length);
  });

  it('has unique IDs across all problems', async () => {
    const problems = await getAllProblems();
    const ids = problems.map((p) => p.id);
    expect(new Set(ids).size).toBe(ids.length);
  });
});

// ---------------------------------------------------------------------------
// getProblemBySlug
// ---------------------------------------------------------------------------

describe('getProblemBySlug', () => {
  it('returns the correct problem for a known slug', async () => {
    const problem = await getProblemBySlug('modus-ponens');
    expect(problem).not.toBeNull();
    expect(problem!.slug).toBe('modus-ponens');
    expect(problem!.category).toBe('logic');
  });

  it('returns null for an unknown slug', async () => {
    const problem = await getProblemBySlug('non-existent-problem');
    expect(problem).toBeNull();
  });

  it('returns null for an empty string', async () => {
    const problem = await getProblemBySlug('');
    expect(problem).toBeNull();
  });
});

// ---------------------------------------------------------------------------
// getProblemSummaries
// ---------------------------------------------------------------------------

describe('getProblemSummaries', () => {
  it('returns summaries with only the expected fields', async () => {
    const summaries = await getProblemSummaries();
    const summaryKeys = ['id', 'slug', 'title', 'difficulty', 'category', 'tags'];

    for (const s of summaries) {
      expect(Object.keys(s).sort()).toEqual(summaryKeys.sort());
    }
  });

  it('does not include problem-detail fields like description or prelude', async () => {
    const summaries = await getProblemSummaries();
    for (const s of summaries) {
      const obj = s as Record<string, unknown>;
      expect(obj.description).toBeUndefined();
      expect(obj.prelude).toBeUndefined();
      expect(obj.template).toBeUndefined();
      expect(obj.solution).toBeUndefined();
      expect(obj.hints).toBeUndefined();
      expect(obj.forbiddenTactics).toBeUndefined();
    }
  });

  it('returns the same count as getAllProblems', async () => {
    const problems = await getAllProblems();
    const summaries = await getProblemSummaries();
    expect(summaries.length).toBe(problems.length);
  });
});

// ---------------------------------------------------------------------------
// getProblemsByCategory
// ---------------------------------------------------------------------------

describe('getProblemsByCategory', () => {
  it('returns only logic problems for category "logic"', () => {
    const logicProblems = getProblemsByCategory('logic');
    expect(logicProblems.length).toBeGreaterThan(0);
    for (const p of logicProblems) {
      expect(p.category).toBe('logic');
    }
  });

  it('returns only induction problems for category "induction"', () => {
    const inductionProblems = getProblemsByCategory('induction');
    expect(inductionProblems.length).toBeGreaterThan(0);
    for (const p of inductionProblems) {
      expect(p.category).toBe('induction');
    }
  });

  it('returns an empty array for a non-existent category', () => {
    const problems = getProblemsByCategory('nonexistent');
    expect(problems).toEqual([]);
  });
});

// ---------------------------------------------------------------------------
// getProblemsByDifficulty
// ---------------------------------------------------------------------------

describe('getProblemsByDifficulty', () => {
  it('returns only easy problems for difficulty "easy"', () => {
    const easyProblems = getProblemsByDifficulty('easy');
    expect(easyProblems.length).toBeGreaterThan(0);
    for (const p of easyProblems) {
      expect(p.difficulty).toBe('easy');
    }
  });

  it('returns only hard problems for difficulty "hard"', () => {
    const hardProblems = getProblemsByDifficulty('hard');
    expect(hardProblems.length).toBeGreaterThan(0);
    for (const p of hardProblems) {
      expect(p.difficulty).toBe('hard');
    }
  });

  it('returns an empty array for a non-existent difficulty', () => {
    const problems = getProblemsByDifficulty('impossible');
    expect(problems).toEqual([]);
  });

  it('all difficulties together cover all problems', async () => {
    const all = await getAllProblems();
    const easy = getProblemsByDifficulty('easy');
    const medium = getProblemsByDifficulty('medium');
    const hard = getProblemsByDifficulty('hard');
    expect(easy.length + medium.length + hard.length).toBe(all.length);
  });
});
