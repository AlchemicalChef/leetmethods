export interface SrsData {
  easeFactor: number;      // starts at 2.5, min 1.3
  interval: number;        // days until next review
  nextReviewAt: number;    // timestamp (ms)
  reviewCount: number;     // total reviews completed
  lastReviewQuality: number; // 0-5
}

const MIN_EASE = 1.3;
const MAX_INTERVAL = 180; // days
const MS_PER_DAY = 86400000;

export function createInitialSrs(): SrsData {
  return {
    easeFactor: 2.5,
    interval: 1,
    nextReviewAt: Date.now() + MS_PER_DAY,
    reviewCount: 0,
    lastReviewQuality: 5,
  };
}

export function deriveQuality(attempts: number, hintsUsed: number): number {
  if (attempts <= 1 && hintsUsed === 0) return 5;
  if (attempts <= 3 || hintsUsed > 0) return 3;
  return 1;
}

export function calculateNextReview(current: SrsData, quality: number): SrsData {
  const reviewCount = current.reviewCount + 1;

  // If quality < 3, reset interval
  if (quality < 3) {
    return {
      easeFactor: Math.max(MIN_EASE, current.easeFactor - 0.2),
      interval: 1,
      nextReviewAt: Date.now() + MS_PER_DAY,
      reviewCount,
      lastReviewQuality: quality,
    };
  }

  // SM-2 ease factor update
  const newEase = Math.max(
    MIN_EASE,
    current.easeFactor + (0.1 - (5 - quality) * (0.08 + (5 - quality) * 0.02))
  );

  // SM-2 interval calculation
  let newInterval: number;
  if (reviewCount === 1) {
    newInterval = 1;
  } else if (reviewCount === 2) {
    newInterval = 6;
  } else {
    newInterval = Math.min(MAX_INTERVAL, Math.round(current.interval * newEase));
  }

  return {
    easeFactor: newEase,
    interval: newInterval,
    nextReviewAt: Date.now() + newInterval * MS_PER_DAY,
    reviewCount,
    lastReviewQuality: quality,
  };
}

export function isReviewDue(srs: SrsData): boolean {
  return Date.now() >= srs.nextReviewAt;
}

export function daysOverdue(srs: SrsData): number {
  const diff = Date.now() - srs.nextReviewAt;
  return Math.max(0, Math.floor(diff / MS_PER_DAY));
}
