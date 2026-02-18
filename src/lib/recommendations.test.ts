import { describe, it, expect } from 'vitest';
import { getNextRecommendation } from './recommendations';
import { makeProblem } from '@/test/factories';

describe('getNextRecommendation', () => {
  // ── Priority 1: same category, same difficulty ──────────────────────

  it('returns a same-category, same-difficulty problem first (priority 1)', () => {
    const current = makeProblem('current', 'logic', 'medium');
    const expected = makeProblem('same-cat-diff', 'logic', 'medium');
    const harder = makeProblem('harder', 'logic', 'hard');
    const otherCat = makeProblem('other-cat', 'induction', 'medium');

    const result = getNextRecommendation(current, [current, expected, harder, otherCat], []);
    expect(result).toEqual(expected);
  });

  it('returns the first same-category, same-difficulty problem when multiple exist', () => {
    const current = makeProblem('current', 'lists', 'easy');
    const first = makeProblem('first', 'lists', 'easy');
    const second = makeProblem('second', 'lists', 'easy');

    const result = getNextRecommendation(current, [current, first, second], []);
    expect(result).toEqual(first);
  });

  // ── Priority 2: same category, harder (sorted ascending) ───────────

  it('returns same-category harder problem when no same-difficulty exists (priority 2)', () => {
    const current = makeProblem('current', 'logic', 'easy');
    const medium = makeProblem('medium-logic', 'logic', 'medium');
    const hard = makeProblem('hard-logic', 'logic', 'hard');

    const result = getNextRecommendation(current, [current, hard, medium], []);
    expect(result).toEqual(medium);
  });

  it('picks the least hard among multiple same-category harder problems', () => {
    const current = makeProblem('current', 'induction', 'easy');
    // Intentionally list hard before medium to verify the sort
    const hard = makeProblem('hard-ind', 'induction', 'hard');
    const medium = makeProblem('med-ind', 'induction', 'medium');

    const result = getNextRecommendation(current, [current, hard, medium], []);
    expect(result).toEqual(medium);
  });

  it('returns hard when current is medium and only hard same-category exists', () => {
    const current = makeProblem('current', 'lists', 'medium');
    const hard = makeProblem('hard-lists', 'lists', 'hard');

    const result = getNextRecommendation(current, [current, hard], []);
    expect(result).toEqual(hard);
  });

  // ── Priority 3: any same category (when only easier exists) ────────

  it('falls back to easier same-category problem when no same or harder difficulty exists (priority 3)', () => {
    const current = makeProblem('current', 'logic', 'hard');
    const easier = makeProblem('easy-logic', 'logic', 'easy');
    const otherCat = makeProblem('other', 'induction', 'hard');

    const result = getNextRecommendation(current, [current, easier, otherCat], []);
    expect(result).toEqual(easier);
  });

  it('returns same-category easier problem even when same-difficulty other-category exists', () => {
    const current = makeProblem('current', 'arithmetic', 'medium');
    const easierSameCat = makeProblem('easy-arith', 'arithmetic', 'easy');
    const sameDiffOtherCat = makeProblem('med-lists', 'lists', 'medium');

    const result = getNextRecommendation(
      current,
      [current, easierSameCat, sameDiffOtherCat],
      []
    );
    expect(result).toEqual(easierSameCat);
  });

  // ── Priority 4: same difficulty, different category ────────────────

  it('returns same-difficulty different-category when no same-category problems exist (priority 4)', () => {
    const current = makeProblem('current', 'logic', 'medium');
    const sameDiff = makeProblem('med-lists', 'lists', 'medium');
    const easy = makeProblem('easy-ind', 'induction', 'easy');

    const result = getNextRecommendation(current, [current, sameDiff, easy], []);
    expect(result).toEqual(sameDiff);
  });

  // ── Priority 5: easiest unsolved overall (fallback) ────────────────

  it('returns the easiest unsolved problem when nothing matches prior priorities (priority 5)', () => {
    const current = makeProblem('current', 'logic', 'medium');
    const hardOther = makeProblem('hard-ind', 'induction', 'hard');
    const easyOther = makeProblem('easy-lists', 'lists', 'easy');

    const result = getNextRecommendation(current, [current, hardOther, easyOther], []);
    expect(result).toEqual(easyOther);
  });

  it('picks easy over hard when both are different category and different difficulty', () => {
    const current = makeProblem('current', 'relations', 'medium');
    // Only hard and easy from other categories
    const hard = makeProblem('hard-arith', 'arithmetic', 'hard');
    const easy = makeProblem('easy-ind', 'induction', 'easy');

    const result = getNextRecommendation(current, [current, hard, easy], []);
    expect(result).toEqual(easy);
  });

  // ── Edge case: all solved ──────────────────────────────────────────

  it('returns null when all problems are completed', () => {
    const current = makeProblem('current', 'logic', 'easy');
    const other = makeProblem('other', 'logic', 'easy');

    const result = getNextRecommendation(current, [current, other], ['other']);
    expect(result).toBeNull();
  });

  // ── Edge case: current problem excluded ────────────────────────────

  it('excludes the current problem from candidates even when it is not in completedSlugs', () => {
    const current = makeProblem('current', 'logic', 'easy');

    const result = getNextRecommendation(current, [current], []);
    expect(result).toBeNull();
  });

  // ── Edge case: only one unsolved ───────────────────────────────────

  it('returns the single unsolved problem when only one candidate remains', () => {
    const current = makeProblem('current', 'logic', 'easy');
    const only = makeProblem('only', 'data-structures', 'hard');

    const result = getNextRecommendation(current, [current, only], []);
    expect(result).toEqual(only);
  });

  // ── Completed slugs filtering ──────────────────────────────────────

  it('filters out completed slugs and recommends next best candidate', () => {
    const current = makeProblem('current', 'logic', 'medium');
    const completedProblem = makeProblem('done', 'logic', 'medium');
    const available = makeProblem('available', 'logic', 'medium');

    const result = getNextRecommendation(
      current,
      [current, completedProblem, available],
      ['done']
    );
    expect(result).toEqual(available);
  });

  it('falls to a lower priority when all higher-priority candidates are completed', () => {
    const current = makeProblem('current', 'logic', 'easy');
    const sameCatSameDiff = makeProblem('logic-easy', 'logic', 'easy');
    const sameCatHarder = makeProblem('logic-medium', 'logic', 'medium');
    const diffCatSameDiff = makeProblem('lists-easy', 'lists', 'easy');

    // Mark both same-category problems as completed
    const result = getNextRecommendation(
      current,
      [current, sameCatSameDiff, sameCatHarder, diffCatSameDiff],
      ['logic-easy', 'logic-medium']
    );
    expect(result).toEqual(diffCatSameDiff);
  });

  // ── Empty problems list ────────────────────────────────────────────

  it('returns null when allProblems contains only the current problem', () => {
    const current = makeProblem('current', 'logic', 'easy');

    const result = getNextRecommendation(current, [current], []);
    expect(result).toBeNull();
  });
});
