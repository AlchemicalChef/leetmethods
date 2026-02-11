/**
 * Progress and streak type definitions for the LeetMethods progress system.
 *
 * These types define the shape of per-problem progress data and streak tracking
 * data that is persisted in localStorage via the `progressStore` (Zustand).
 *
 * Important architectural note: This file lives in `src/lib/types/` (not in
 * `src/store/`) because these types are shared across both the store layer and
 * the library layer. The `lib/` directory must not import from `store/`, so
 * shared types must live in `lib/`.
 *
 * The progress store persists data at version 3 (v3). Schema migrations from
 * earlier versions (v2 -> v3 adds SRS fields) are handled in the store itself.
 *
 * @module types/progress
 */

import type { SrsData } from '@/lib/srs';

/* ============================================================================
 * Per-Problem Progress
 * ========================================================================= */

/**
 * Tracks the user's progress on a single problem.
 *
 * One `ProblemProgress` entry exists per problem slug in the progress store.
 * Fields are updated by the problem solver UI and the spaced repetition system.
 *
 * @property slug - The problem's unique slug (matches the key in the progress record).
 * @property completed - Whether the user has successfully verified a correct proof.
 * @property completedAt - Unix timestamp (ms) of the first successful completion,
 *                         or `null` if not yet completed.
 * @property attempts - Total number of submission attempts (incremented each time
 *                      the user clicks "Submit" / "Verify"). Includes failed attempts.
 * @property hintsUsed - Number of hints the user has revealed for this problem.
 *                       Once a hint is revealed, this counter is never decremented.
 * @property solveStartedAt - Unix timestamp (ms) when the user first started working
 *                            on this problem (set on the first submission attempt),
 *                            or `null` if no attempt has been made.
 * @property solveDurationMs - Time from first attempt to successful completion in
 *                             milliseconds, or `null` if not yet completed or if
 *                             timing data was not available.
 * @property srs - Spaced repetition scheduling data for this problem, or `null`
 *                 if the problem has not been completed (SRS is only initialized
 *                 upon first successful completion).
 * @property reviewAttempts - Number of submission attempts during the current or
 *                            most recent review session (reset at the start of
 *                            each new review).
 * @property reviewHintsUsed - Number of hints revealed during the current or most
 *                             recent review session (reset at the start of each
 *                             new review).
 * @property isReviewing - Whether this problem is currently being reviewed (as
 *                         opposed to being solved for the first time). Affects
 *                         UI display and which counters are incremented.
 */
export interface ProblemProgress {
  slug: string;
  completed: boolean;
  completedAt: number | null;
  attempts: number;
  hintsUsed: number;
  solveStartedAt: number | null;
  solveDurationMs: number | null;
  srs: SrsData | null;
  reviewAttempts: number;
  reviewHintsUsed: number;
  isReviewing: boolean;
}

/* ============================================================================
 * Streak Tracking
 * ========================================================================= */

/**
 * Tracks the user's daily solve streak.
 *
 * A "streak" is the number of consecutive calendar days on which the user
 * has completed at least one problem. The streak is updated each time a
 * problem is completed, comparing the completion date against `lastSolveDate`.
 *
 * @property currentStreak - Number of consecutive days with at least one solve,
 *                           ending at `lastSolveDate`. Resets to 1 if the user
 *                           skips a day.
 * @property longestStreak - All-time longest streak in days. Only increases,
 *                           never decreases.
 * @property lastSolveDate - ISO date string (YYYY-MM-DD) of the most recent
 *                           day a problem was solved, or `null` if no problem
 *                           has ever been completed.
 */
export interface StreakData {
  currentStreak: number;
  longestStreak: number;
  lastSolveDate: string | null;
}

/* ============================================================================
 * Review Information
 * ========================================================================= */

/**
 * Lightweight representation of a problem that is due for spaced repetition review.
 *
 * Used to pass review information to UI components without exposing the full
 * `SrsData` object.
 *
 * @property slug - The problem's slug identifier.
 * @property overdueDays - Number of full days past the scheduled review date.
 *                         Higher values indicate more urgent reviews.
 */
export interface DueReviewInfo {
  slug: string;
  overdueDays: number;
}
