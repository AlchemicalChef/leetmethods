/**
 * SM-2 Spaced Repetition Algorithm for LeetMethods.
 *
 * Implements a modified version of the SuperMemo SM-2 algorithm to schedule
 * review sessions for completed Coq proofs. The goal is to help users retain
 * proof techniques over time by presenting problems at increasing intervals
 * based on recall quality.
 *
 * The SM-2 algorithm works as follows:
 * 1. After each review, the user's performance is rated on a 0-5 quality scale.
 * 2. If quality < 3 (poor recall), the interval resets to 1 day and the ease
 *    factor decreases, indicating the problem is harder to retain.
 * 3. If quality >= 3 (adequate recall), the interval grows by multiplying
 *    the previous interval by the ease factor.
 * 4. The ease factor adjusts based on performance quality, with a minimum
 *    floor of 1.3 to prevent intervals from shrinking too aggressively.
 *
 * Key modifications from standard SM-2:
 * - Quality is derived automatically from attempt count and hint usage
 *   (see `deriveQuality`), rather than requiring the user to self-assess.
 * - Maximum interval is capped at 180 days to ensure periodic review.
 * - A migration function (`createMigratedSrs`) staggers initial reviews
 *   for pre-existing completions to avoid overwhelming users.
 *
 * @module srs/algorithm
 */

/* ============================================================================
 * Type Definitions
 * ========================================================================= */

/**
 * Spaced repetition scheduling data for a single problem.
 *
 * This is persisted as part of `ProblemProgress` in the progress store.
 *
 * @property easeFactor - The SM-2 ease factor, starting at 2.5. Lower values mean
 *                        the problem is harder to retain. Minimum: 1.3.
 * @property interval - Number of days until the next review is due.
 * @property nextReviewAt - Unix timestamp (milliseconds) when the next review becomes due.
 * @property reviewCount - Total number of completed reviews for this problem.
 * @property lastReviewQuality - The quality score (0-5) from the most recent review.
 *                               Used by achievement checks for "perfect recall".
 */
export interface SrsData {
  easeFactor: number;
  interval: number;
  nextReviewAt: number;
  reviewCount: number;
  lastReviewQuality: number;
}

/* ============================================================================
 * Constants
 * ========================================================================= */

/** Minimum ease factor to prevent intervals from shrinking too aggressively. */
const MIN_EASE = 1.3;

/** Maximum review interval in days to ensure periodic review even for well-known problems. */
const MAX_INTERVAL = 180;

/** Number of milliseconds in one day, used for timestamp arithmetic. */
const MS_PER_DAY = 86400000;

/* ============================================================================
 * SRS Lifecycle Functions
 * ========================================================================= */

/**
 * Creates initial SRS data for a newly completed problem.
 *
 * Sets the first review for 1 day from now with default SM-2 starting values.
 * The `lastReviewQuality` is set to 5 (perfect) because the initial solve
 * is considered the "first exposure" -- the first real review happens later.
 *
 * @returns Fresh `SrsData` with default starting values.
 */
export function createInitialSrs(): SrsData {
  return {
    easeFactor: 2.5,
    interval: 1,
    nextReviewAt: Date.now() + MS_PER_DAY,
    reviewCount: 0,
    lastReviewQuality: 5,
  };
}

/* ============================================================================
 * Quality Derivation
 * ========================================================================= */

/**
 * Derives a quality score (0-5) from the user's performance during a review session.
 *
 * Instead of asking the user to self-assess (which is subjective and adds friction),
 * quality is inferred from objective metrics:
 *
 * - **5 (perfect)**: Solved on first attempt with no hints -- strong recall.
 * - **3 (adequate)**: Solved within 3 attempts using at most 1 hint -- partial recall.
 * - **1 (poor)**: Required more than 3 attempts or 2+ hints -- needs more practice.
 *
 * The quality thresholds are deliberately coarse (only 3 levels used out of 6)
 * because the attempt/hint metrics are noisy proxies for true recall quality.
 *
 * @param attempts - Number of submission attempts during this review session.
 * @param hintsUsed - Number of hints the user revealed during this review session.
 * @returns A quality score: 5, 3, or 1.
 */
export function deriveQuality(attempts: number, hintsUsed: number): number {
  if (attempts <= 1 && hintsUsed === 0) return 5;
  if (attempts <= 3 && hintsUsed <= 1) return 3;
  return 1;
}

/* ============================================================================
 * Core SM-2 Scheduling
 * ========================================================================= */

/**
 * Calculates the next review schedule after a review is completed.
 *
 * Implements the SM-2 algorithm with the following behavior:
 *
 * **Poor recall (quality < 3):**
 * - Resets the interval to 1 day (re-learn the problem).
 * - Decreases the ease factor by 0.2 (down to the minimum of 1.3).
 *
 * **Adequate recall (quality >= 3):**
 * - Updates the ease factor using the SM-2 formula:
 *   `EF' = EF + (0.1 - (5 - q) * (0.08 + (5 - q) * 0.02))`
 *   where `q` is the quality score and `EF` is the current ease factor.
 * - Calculates the new interval:
 *   - 1st review: 1 day
 *   - 2nd review: 6 days
 *   - Subsequent: `previous_interval * ease_factor` (capped at MAX_INTERVAL)
 *
 * @param current - The current SRS data for the problem.
 * @param quality - The quality score (0-5) for this review session.
 * @returns Updated `SrsData` with the new schedule.
 */
export function calculateNextReview(current: SrsData, quality: number): SrsData {
  const reviewCount = current.reviewCount + 1;

  /* Poor recall: reset to short interval and penalize ease factor */
  if (quality < 3) {
    return {
      easeFactor: Math.max(MIN_EASE, current.easeFactor - 0.2),
      interval: 1,
      nextReviewAt: Date.now() + MS_PER_DAY,
      reviewCount,
      lastReviewQuality: quality,
    };
  }

  /**
   * SM-2 ease factor adjustment formula.
   * For quality=5: EF increases by 0.1 (problem is getting easier).
   * For quality=3: EF decreases by 0.14 (problem needs more reinforcement).
   * The result is clamped to MIN_EASE to prevent excessively short intervals.
   */
  const newEase = Math.max(
    MIN_EASE,
    current.easeFactor + (0.1 - (5 - quality) * (0.08 + (5 - quality) * 0.02))
  );

  /**
   * SM-2 interval progression:
   * - Review 1: Always 1 day (immediate reinforcement after first solve).
   * - Review 2: Always 6 days (standard SM-2 second interval).
   * - Review 3+: Multiply previous interval by the ease factor, capped at MAX_INTERVAL.
   */
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

/* ============================================================================
 * Migration Support
 * ========================================================================= */

/**
 * Creates SRS data for a problem that was completed before the SRS system existed.
 *
 * When the progress store migrates from v2 to v3 (adding SRS fields), all
 * previously completed problems need initial SRS data. To avoid overwhelming
 * the user with all reviews becoming due on the same day, this function
 * staggers the `nextReviewAt` timestamps across a 14-day window based on
 * the problem's index in the migration batch.
 *
 * @param index - The problem's position in the migration batch (0-based).
 *                Used to calculate the stagger offset via `(index % 14) + 1`.
 * @returns SRS data with a staggered first review date.
 */
export function createMigratedSrs(index: number): SrsData {
  const staggerDays = 1 + (index % 14);
  return {
    easeFactor: 2.5,
    interval: staggerDays,
    nextReviewAt: Date.now() + staggerDays * MS_PER_DAY,
    reviewCount: 0,
    lastReviewQuality: 5,
  };
}

/* ============================================================================
 * Due Date Queries
 * ========================================================================= */

/**
 * Checks whether a problem's review is currently due.
 *
 * A review is due when the current time has passed the scheduled `nextReviewAt`
 * timestamp.
 *
 * @param srs - The SRS data for the problem.
 * @returns `true` if the review is due (or overdue), `false` otherwise.
 */
export function isReviewDue(srs: SrsData): boolean {
  return Date.now() >= srs.nextReviewAt;
}

/**
 * Calculates how many full days overdue a review is.
 *
 * Returns 0 if the review is not yet due. This value is used to prioritize
 * the most overdue reviews first in the review queue.
 *
 * @param srs - The SRS data for the problem.
 * @returns Number of full days past the scheduled review date (minimum 0).
 */
export function daysOverdue(srs: SrsData): number {
  const diff = Date.now() - srs.nextReviewAt;
  return Math.max(0, Math.floor(diff / MS_PER_DAY));
}
