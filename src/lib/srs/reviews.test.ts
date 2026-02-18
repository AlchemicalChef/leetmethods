import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { getDueProblems, getReviewStats } from './reviews';
import type { SrsData } from './algorithm';

const FIXED_TIME = new Date('2026-02-17T12:00:00Z').getTime();
const MS_PER_DAY = 86400000;

const makeSrs = (overrides?: Partial<SrsData>): SrsData => ({
  easeFactor: 2.5,
  interval: 1,
  nextReviewAt: FIXED_TIME,
  reviewCount: 0,
  lastReviewQuality: 5,
  ...overrides,
});

describe('getDueProblems', () => {
  beforeEach(() => {
    vi.useFakeTimers();
    vi.setSystemTime(FIXED_TIME);
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  it('returns empty array for empty srsMap', () => {
    expect(getDueProblems({})).toEqual([]);
  });

  it('returns empty array when no problems are due', () => {
    const srsMap = {
      'p1': makeSrs({ nextReviewAt: FIXED_TIME + MS_PER_DAY }),
      'p2': makeSrs({ nextReviewAt: FIXED_TIME + 2 * MS_PER_DAY }),
    };
    expect(getDueProblems(srsMap)).toEqual([]);
  });

  it('returns due problems', () => {
    const srsMap = {
      'p1': makeSrs({ nextReviewAt: FIXED_TIME - MS_PER_DAY }),
      'p2': makeSrs({ nextReviewAt: FIXED_TIME }),
      'p3': makeSrs({ nextReviewAt: FIXED_TIME + MS_PER_DAY }),
    };
    const result = getDueProblems(srsMap);
    expect(result).toHaveLength(2);
    expect(result.map(r => r.slug)).toContain('p1');
    expect(result.map(r => r.slug)).toContain('p2');
  });

  it('sorts by most overdue first', () => {
    const srsMap = {
      'p1': makeSrs({ nextReviewAt: FIXED_TIME - MS_PER_DAY }),
      'p2': makeSrs({ nextReviewAt: FIXED_TIME - 3 * MS_PER_DAY }),
      'p3': makeSrs({ nextReviewAt: FIXED_TIME - 2 * MS_PER_DAY }),
    };
    const result = getDueProblems(srsMap);
    expect(result[0].slug).toBe('p2');
    expect(result[1].slug).toBe('p3');
    expect(result[2].slug).toBe('p1');
  });

  it('caps at 5 problems (DAILY_REVIEW_CAP)', () => {
    const srsMap: Record<string, SrsData> = {};
    for (let i = 1; i <= 10; i++) {
      srsMap[`p${i}`] = makeSrs({ nextReviewAt: FIXED_TIME - i * MS_PER_DAY });
    }
    expect(getDueProblems(srsMap)).toHaveLength(5);
  });

  it('reduces cap by completedToday', () => {
    const srsMap: Record<string, SrsData> = {};
    for (let i = 1; i <= 10; i++) {
      srsMap[`p${i}`] = makeSrs({ nextReviewAt: FIXED_TIME - i * MS_PER_DAY });
    }
    expect(getDueProblems(srsMap, 3)).toHaveLength(2);
  });

  it('returns empty array when completedToday >= 5', () => {
    const srsMap = {
      'p1': makeSrs({ nextReviewAt: FIXED_TIME - MS_PER_DAY }),
    };
    expect(getDueProblems(srsMap, 5)).toEqual([]);
    expect(getDueProblems(srsMap, 10)).toEqual([]);
  });

  it('each DueReview has correct slug, srs, and overdueDays', () => {
    const srs1 = makeSrs({ nextReviewAt: FIXED_TIME - 2 * MS_PER_DAY });
    const srsMap = { 'p1': srs1 };
    const result = getDueProblems(srsMap);
    expect(result).toHaveLength(1);
    expect(result[0].slug).toBe('p1');
    expect(result[0].srs).toEqual(srs1);
    expect(result[0].overdueDays).toBe(2);
  });

  it('handles problems due exactly now (overdueDays = 0)', () => {
    const srsMap = { 'p1': makeSrs({ nextReviewAt: FIXED_TIME }) };
    const result = getDueProblems(srsMap);
    expect(result).toHaveLength(1);
    expect(result[0].overdueDays).toBe(0);
  });
});

describe('getReviewStats', () => {
  beforeEach(() => {
    vi.useFakeTimers();
    vi.setSystemTime(FIXED_TIME);
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  it('returns default values for empty srsMap', () => {
    expect(getReviewStats({})).toEqual({
      totalReviews: 0,
      dueCount: 0,
      dailyCapReached: false,
      averageEase: 2.5,
    });
  });

  it('sums totalReviews from reviewCount fields', () => {
    const srsMap = {
      'p1': makeSrs({ reviewCount: 3 }),
      'p2': makeSrs({ reviewCount: 5 }),
      'p3': makeSrs({ reviewCount: 2 }),
    };
    expect(getReviewStats(srsMap).totalReviews).toBe(10);
  });

  it('counts due problems correctly', () => {
    const srsMap = {
      'p1': makeSrs({ nextReviewAt: FIXED_TIME - MS_PER_DAY }),
      'p2': makeSrs({ nextReviewAt: FIXED_TIME }),
      'p3': makeSrs({ nextReviewAt: FIXED_TIME + MS_PER_DAY }),
    };
    expect(getReviewStats(srsMap).dueCount).toBe(2);
  });

  it('computes average ease factor', () => {
    const srsMap = {
      'p1': makeSrs({ easeFactor: 2.0 }),
      'p2': makeSrs({ easeFactor: 2.5 }),
      'p3': makeSrs({ easeFactor: 3.0 }),
    };
    expect(getReviewStats(srsMap).averageEase).toBeCloseTo(2.5);
  });

  it('dailyCapReached is always false', () => {
    const srsMap = {
      'p1': makeSrs({ nextReviewAt: FIXED_TIME - MS_PER_DAY }),
      'p2': makeSrs({ nextReviewAt: FIXED_TIME - 2 * MS_PER_DAY }),
    };
    expect(getReviewStats(srsMap).dailyCapReached).toBe(false);
  });

  it('handles single problem', () => {
    const srsMap = { 'p1': makeSrs({ reviewCount: 5, easeFactor: 2.8 }) };
    const result = getReviewStats(srsMap);
    expect(result.totalReviews).toBe(5);
    expect(result.averageEase).toBe(2.8);
  });
});
