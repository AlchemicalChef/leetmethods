import { describe, it, expect } from 'vitest';
import {
  getAllProblems,
  getProblemSummaries,
} from './loader';

// ---------------------------------------------------------------------------
// getAllProblems
// ---------------------------------------------------------------------------

describe('getAllProblems', () => {
  it('returns an array of problems', () => {
    const problems = getAllProblems();
    expect(Array.isArray(problems)).toBe(true);
    expect(problems.length).toBeGreaterThan(0);
  });

  it('every problem has all required fields', () => {
    const problems = getAllProblems();
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

  it('has unique slugs across all problems', () => {
    const problems = getAllProblems();
    const slugs = problems.map((p) => p.slug);
    expect(new Set(slugs).size).toBe(slugs.length);
  });

  it('has unique IDs across all problems', () => {
    const problems = getAllProblems();
    const ids = problems.map((p) => p.id);
    expect(new Set(ids).size).toBe(ids.length);
  });
});

// ---------------------------------------------------------------------------
// getProblemSummaries
// ---------------------------------------------------------------------------

describe('getProblemSummaries', () => {
  it('returns summaries with only the expected fields', () => {
    const summaries = getProblemSummaries();
    const summaryKeys = ['id', 'slug', 'title', 'difficulty', 'category', 'tags'];

    for (const s of summaries) {
      expect(Object.keys(s).sort()).toEqual(summaryKeys.sort());
    }
  });

  it('does not include problem-detail fields like description or prelude', () => {
    const summaries = getProblemSummaries();
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

  it('returns the same count as getAllProblems', () => {
    const problems = getAllProblems();
    const summaries = getProblemSummaries();
    expect(summaries.length).toBe(problems.length);
  });
});
