import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import {
  createInitialSrs,
  deriveQuality,
  calculateNextReview,
  createMigratedSrs,
  isReviewDue,
  daysOverdue,
} from './algorithm';
import type { SrsData } from './algorithm';

const MS_PER_DAY = 86400000;

describe('SRS Algorithm', () => {
  beforeEach(() => {
    vi.useFakeTimers();
    vi.setSystemTime(new Date('2025-06-15T12:00:00Z'));
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  describe('createInitialSrs', () => {
    it('returns correct initial values', () => {
      const srs = createInitialSrs();
      expect(srs.easeFactor).toBe(2.5);
      expect(srs.interval).toBe(1);
      expect(srs.reviewCount).toBe(0);
      expect(srs.lastReviewQuality).toBe(5);
    });

    it('sets nextReviewAt to 1 day from now', () => {
      const now = Date.now();
      const srs = createInitialSrs();
      expect(srs.nextReviewAt).toBe(now + MS_PER_DAY);
    });
  });

  describe('deriveQuality', () => {
    it('returns 5 for 1 attempt and 0 hints', () => {
      expect(deriveQuality(1, 0)).toBe(5);
    });

    it('returns 5 for 0 attempts and 0 hints', () => {
      expect(deriveQuality(0, 0)).toBe(5);
    });

    it('returns 3 for 2 attempts and 0 hints', () => {
      expect(deriveQuality(2, 0)).toBe(3);
    });

    it('returns 3 for 3 attempts and 1 hint (boundary)', () => {
      expect(deriveQuality(3, 1)).toBe(3);
    });

    it('returns 3 for 1 attempt and 1 hint', () => {
      expect(deriveQuality(1, 1)).toBe(3);
    });

    it('returns 1 for 4 attempts and 0 hints', () => {
      expect(deriveQuality(4, 0)).toBe(1);
    });

    it('returns 1 for 1 attempt and 2 hints', () => {
      expect(deriveQuality(1, 2)).toBe(1);
    });

    it('returns 1 for 5 attempts and 3 hints', () => {
      expect(deriveQuality(5, 3)).toBe(1);
    });
  });

  describe('calculateNextReview', () => {
    const baseSrs = (overrides?: Partial<SrsData>): SrsData => ({
      easeFactor: 2.5,
      interval: 1,
      nextReviewAt: Date.now(),
      reviewCount: 0,
      lastReviewQuality: 5,
      ...overrides,
    });

    it('resets interval to 1 for poor quality (q < 3)', () => {
      const result = calculateNextReview(baseSrs({ interval: 10, reviewCount: 5 }), 1);
      expect(result.interval).toBe(1);
    });

    it('decreases easeFactor by 0.2 for poor quality', () => {
      const result = calculateNextReview(baseSrs({ easeFactor: 2.5 }), 1);
      expect(result.easeFactor).toBe(2.3);
    });

    it('does not drop easeFactor below 1.3 on poor quality', () => {
      const result = calculateNextReview(baseSrs({ easeFactor: 1.3 }), 0);
      expect(result.easeFactor).toBe(1.3);
    });

    it('sets interval to 1 for first review with good quality', () => {
      const result = calculateNextReview(baseSrs({ reviewCount: 0 }), 5);
      expect(result.interval).toBe(1);
      expect(result.reviewCount).toBe(1);
    });

    it('sets interval to 6 for second review with good quality', () => {
      const result = calculateNextReview(baseSrs({ reviewCount: 1 }), 5);
      expect(result.interval).toBe(6);
      expect(result.reviewCount).toBe(2);
    });

    it('calculates interval as round(interval * easeFactor) for third+ review', () => {
      const current = baseSrs({ easeFactor: 2.5, interval: 6, reviewCount: 2 });
      const result = calculateNextReview(current, 5);
      // easeFactor increases to 2.6, then interval = round(6 * 2.6) = 16
      expect(result.interval).toBe(Math.round(6 * 2.6));
      expect(result.reviewCount).toBe(3);
    });

    it('increases easeFactor by 0.1 for quality 5', () => {
      const result = calculateNextReview(baseSrs({ easeFactor: 2.5 }), 5);
      expect(result.easeFactor).toBe(2.6);
    });

    it('decreases easeFactor for quality 3', () => {
      const result = calculateNextReview(baseSrs({ easeFactor: 2.5 }), 3);
      expect(result.easeFactor).toBeLessThan(2.5);
      expect(result.easeFactor).toBeGreaterThanOrEqual(1.3);
    });

    it('caps interval at 180 days', () => {
      const current = baseSrs({ easeFactor: 3.0, interval: 100, reviewCount: 10 });
      const result = calculateNextReview(current, 5);
      expect(result.interval).toBeLessThanOrEqual(180);
    });

    it('always increments reviewCount', () => {
      const result = calculateNextReview(baseSrs({ reviewCount: 7 }), 5);
      expect(result.reviewCount).toBe(8);
    });

    it('stores lastReviewQuality', () => {
      const result = calculateNextReview(baseSrs(), 3);
      expect(result.lastReviewQuality).toBe(3);
    });

    it('sets nextReviewAt based on new interval', () => {
      const now = Date.now();
      const result = calculateNextReview(baseSrs({ reviewCount: 0 }), 5);
      expect(result.nextReviewAt).toBe(now + result.interval * MS_PER_DAY);
    });
  });

  describe('createMigratedSrs', () => {
    it('staggers index 0 by 1 day', () => {
      const now = Date.now();
      const srs = createMigratedSrs(0);
      expect(srs.interval).toBe(1);
      expect(srs.nextReviewAt).toBe(now + MS_PER_DAY);
    });

    it('staggers index 13 by 14 days', () => {
      const now = Date.now();
      const srs = createMigratedSrs(13);
      expect(srs.interval).toBe(14);
      expect(srs.nextReviewAt).toBe(now + 14 * MS_PER_DAY);
    });

    it('wraps index 14 back to 1 day', () => {
      const now = Date.now();
      const srs = createMigratedSrs(14);
      expect(srs.interval).toBe(1);
      expect(srs.nextReviewAt).toBe(now + MS_PER_DAY);
    });

    it('always has easeFactor 2.5 and reviewCount 0', () => {
      const srs = createMigratedSrs(5);
      expect(srs.easeFactor).toBe(2.5);
      expect(srs.reviewCount).toBe(0);
      expect(srs.lastReviewQuality).toBe(5);
    });
  });

  describe('isReviewDue', () => {
    const makeSrs = (nextReviewAt: number): SrsData => ({
      easeFactor: 2.5, interval: 1, nextReviewAt, reviewCount: 0, lastReviewQuality: 5,
    });

    it('returns true for past nextReviewAt', () => {
      expect(isReviewDue(makeSrs(Date.now() - 1000))).toBe(true);
    });

    it('returns false for future nextReviewAt', () => {
      expect(isReviewDue(makeSrs(Date.now() + 1000))).toBe(false);
    });

    it('returns true for exactly now (>=)', () => {
      expect(isReviewDue(makeSrs(Date.now()))).toBe(true);
    });
  });

  describe('daysOverdue', () => {
    const makeSrs = (nextReviewAt: number): SrsData => ({
      easeFactor: 2.5, interval: 1, nextReviewAt, reviewCount: 0, lastReviewQuality: 5,
    });

    it('returns 0 when not due yet', () => {
      expect(daysOverdue(makeSrs(Date.now() + MS_PER_DAY))).toBe(0);
    });

    it('returns 1 for 1 day overdue', () => {
      expect(daysOverdue(makeSrs(Date.now() - MS_PER_DAY))).toBe(1);
    });

    it('floors partial days (0.5 days → 0)', () => {
      expect(daysOverdue(makeSrs(Date.now() - MS_PER_DAY * 0.5))).toBe(0);
    });

    it('returns correct value for multiple days overdue', () => {
      expect(daysOverdue(makeSrs(Date.now() - MS_PER_DAY * 5))).toBe(5);
    });
  });
});
