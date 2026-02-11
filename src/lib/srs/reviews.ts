/**
 * Review queue management for the spaced repetition system.
 *
 * This module builds on top of the core SM-2 algorithm to provide higher-level
 * functions for managing the daily review workflow:
 *
 * - **Queue building**: Determines which problems are due for review, sorted
 *   by urgency (most overdue first).
 * - **Daily cap enforcement**: Limits the number of reviews per day to prevent
 *   burnout. The cap is applied after sorting, so the most urgent reviews are
 *   always presented first.
 * - **Review statistics**: Aggregates SRS data across all problems for dashboard
 *   display (total reviews completed, number due, average ease factor).
 *
 * This module is used by the progress store and UI components to display review
 * counts and build the review queue on the problems page.
 *
 * @module srs/reviews
 */

import type { SrsData } from './algorithm';
import { isReviewDue, daysOverdue } from './algorithm';

/* ============================================================================
 * Constants
 * ========================================================================= */

/**
 * Maximum number of reviews to present per day.
 *
 * This prevents "review debt" from becoming overwhelming if a user misses
 * several days. Without a cap, returning after a week off could present
 * 20+ reviews, which is discouraging. The cap ensures a manageable daily load.
 */
const DAILY_REVIEW_CAP = 5;

/* ============================================================================
 * Type Definitions
 * ========================================================================= */

/**
 * A single problem that is due for spaced repetition review.
 *
 * @property slug - The problem's unique slug identifier.
 * @property srs - The problem's current SRS scheduling data.
 * @property overdueDays - Number of full days past the scheduled review date.
 *                         Used for sorting by urgency (most overdue first).
 */
export interface DueReview {
  slug: string;
  srs: SrsData;
  overdueDays: number;
}

/**
 * Aggregated statistics about the user's spaced repetition state.
 *
 * @property totalReviews - Sum of `reviewCount` across all SRS entries.
 * @property dueCount - Number of problems currently due for review (before cap).
 * @property dailyCapReached - Whether the daily review cap has been reached.
 *                             Defaults to `false`; the caller should override
 *                             based on the number of reviews completed today.
 * @property averageEase - Average ease factor across all SRS entries. Defaults
 *                         to 2.5 (the SM-2 starting value) when there are no entries.
 */
export interface ReviewStats {
  totalReviews: number;
  dueCount: number;
  dailyCapReached: boolean;
  averageEase: number;
}

/* ============================================================================
 * Review Queue Functions
 * ========================================================================= */

/**
 * Builds the list of problems due for review, sorted by urgency and capped
 * at the daily limit.
 *
 * The returned list is sorted with the most overdue problems first, ensuring
 * that the user addresses the highest-priority reviews. The daily cap accounts
 * for reviews already completed today, so the caller should pass the count of
 * today's completed reviews to get an accurate remaining allowance.
 *
 * @param srsMap - A record mapping problem slugs to their SRS data.
 *                 Only problems with SRS data are considered (problems without
 *                 SRS data have never been completed and are not eligible for review).
 * @param completedToday - The number of reviews already completed today. Defaults to 0.
 *                         Subtracted from the daily cap to determine how many more
 *                         reviews to return.
 * @returns An array of `DueReview` objects, sorted by `overdueDays` descending,
 *          limited to the remaining daily allowance.
 */
export function getDueProblems(
  srsMap: Record<string, SrsData>,
  completedToday: number = 0
): DueReview[] {
  const due: DueReview[] = [];
  for (const [slug, srs] of Object.entries(srsMap)) {
    if (isReviewDue(srs)) {
      due.push({ slug, srs, overdueDays: daysOverdue(srs) });
    }
  }

  /* Sort by urgency: most overdue reviews should be presented first */
  due.sort((a, b) => b.overdueDays - a.overdueDays);

  /* Apply daily cap, accounting for reviews already completed today */
  const remaining = Math.max(0, DAILY_REVIEW_CAP - completedToday);
  return due.slice(0, remaining);
}

/* ============================================================================
 * Review Statistics
 * ========================================================================= */

/**
 * Computes aggregate statistics about the user's spaced repetition state.
 *
 * This is used by the stats page and review dashboard to display summary metrics.
 * Note that `dailyCapReached` is always returned as `false` here because this
 * function does not have access to the count of today's completed reviews;
 * the caller should override it if needed.
 *
 * @param srsMap - A record mapping problem slugs to their SRS data.
 * @returns Aggregated review statistics.
 */
export function getReviewStats(srsMap: Record<string, SrsData>): ReviewStats {
  const entries = Object.values(srsMap);
  const totalReviews = entries.reduce((sum, s) => sum + s.reviewCount, 0);
  const dueCount = entries.filter((s) => isReviewDue(s)).length;

  /**
   * Average ease factor gives a rough sense of overall retention quality.
   * A declining average suggests the user is struggling; a stable or
   * increasing average indicates strong recall. Falls back to the default
   * SM-2 starting ease (2.5) when there are no SRS entries.
   */
  const averageEase = entries.length > 0
    ? entries.reduce((sum, s) => sum + s.easeFactor, 0) / entries.length
    : 2.5;

  return {
    totalReviews,
    dueCount,
    dailyCapReached: false,
    averageEase,
  };
}
