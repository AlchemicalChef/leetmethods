import { describe, it, expect } from 'vitest';
import {
  getAllProblems,
  getProblemSummaries,
  getAllProblemsSync,
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
      expect(['logic', 'induction', 'lists', 'arithmetic', 'data-structures', 'relations', 'booleans']).toContain(p.category);
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
// getAllProblemsSync
// ---------------------------------------------------------------------------

describe('getAllProblemsSync', () => {
  it('returns the same problems as getAllProblems', async () => {
    const asyncProblems = await getAllProblems();
    const syncProblems = getAllProblemsSync();
    expect(syncProblems.length).toBe(asyncProblems.length);
    expect(syncProblems.map((p) => p.slug).sort()).toEqual(asyncProblems.map((p) => p.slug).sort());
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
      const obj = s as unknown as Record<string, unknown>;
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
