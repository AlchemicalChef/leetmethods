/**
 * @module progressStore
 *
 * Persisted Zustand store that tracks per-problem progress, solve timers,
 * spaced-repetition scheduling (SRS), and daily streak data.
 *
 * This is the most complex store in LeetMethods. It is persisted to localStorage
 * via the `zustand/middleware/persist` middleware using `safeStorage` (a wrapper
 * that gracefully handles `QuotaExceededError` on write). The store has gone
 * through multiple schema versions, with explicit migrations for each upgrade:
 *
 *   v1 -> v2: Added timer fields (solveStartedAt, solveDurationMs) and streakData.
 *   v2 -> v3: Added SRS fields (srs, reviewAttempts, reviewHintsUsed, isReviewing).
 *             Already-completed problems get staggered initial SRS schedules to
 *             avoid flooding the user with all reviews on the same day.
 *
 * Architecture notes:
 * - The `progress` record is keyed by problem slug (e.g. "nat-add-comm").
 * - Each `ProblemProgress` entry tracks completion status, attempt/hint counts,
 *   solve timing, and SRS scheduling metadata.
 * - The `streakData` object tracks the user's daily solve streak, updated
 *   whenever a problem is marked as completed.
 * - SRS (Spaced Repetition System) uses a modified SM-2 algorithm. Quality
 *   scores are derived from the number of review attempts and hints used.
 * - Due reviews are capped at DAILY_REVIEW_CAP to prevent overwhelming the user.
 * - Timer design: `solveStartedAt` records when the user began working;
 *   `solveDurationMs` accumulates elapsed time. The timer can be paused
 *   (stopTimer) and resumed (startTimer), allowing accurate tracking even
 *   if the user navigates away and returns.
 *
 * Important: `lib/` modules must not import from `store/` -- shared types
 * live in `src/lib/types/progress.ts` and are re-exported from here.
 */

import { create } from 'zustand';
import { persist } from 'zustand/middleware';
import { safeStorage } from '@/lib/safe-storage';
import { createInitialSrs, createMigratedSrs, calculateNextReview, deriveQuality, isReviewDue, daysOverdue } from '@/lib/srs';
import type { ProblemProgress, StreakData, DueReviewInfo } from '@/lib/types/progress';

/* ─── Re-exports ────────────────────────────────────────────────────────────
 * Re-export progress types so consumers can import them from the store
 * module directly rather than reaching into lib/types.
 * ──────────────────────────────────────────────────────────────────────── */
export type { ProblemProgress, StreakData, DueReviewInfo };

/**
 * Maximum number of due reviews returned by `getDueReviews()` per day.
 * This prevents the review queue from becoming overwhelming when many
 * problems come due simultaneously (e.g., after a vacation).
 */
const DAILY_REVIEW_CAP = 5;

/* ─── Store Interface ───────────────────────────────────────────────────── */

interface ProgressState {
  /** Map from problem slug to its progress record. */
  progress: Record<string, ProblemProgress>;

  /** Tracks the user's daily solve streak (current, longest, last solve date). */
  streakData: StreakData;

  /**
   * Retrieve the progress record for a specific problem.
   * @param slug - The problem's unique slug identifier.
   * @returns The progress record, or undefined if the user has never interacted with this problem.
   */
  getProgress: (slug: string) => ProblemProgress | undefined;

  /**
   * Mark a problem as completed. Handles first-time completion and review
   * completion. Does not increment attempts (that is done separately by the
   * submission handler to avoid double-counting).
   * @param slug - The problem's unique slug identifier.
   */
  markCompleted: (slug: string) => void;

  /**
   * Increment the attempt counter for a problem's initial solve.
   * @param slug - The problem's unique slug identifier.
   */
  incrementAttempts: (slug: string) => void;

  /**
   * Increment the hint-used counter for a problem's initial solve.
   * @param slug - The problem's unique slug identifier.
   */
  incrementHints: (slug: string) => void;

  /**
   * Increment the attempt counter for a problem's review session.
   * @param slug - The problem's unique slug identifier.
   */
  incrementReviewAttempts: (slug: string) => void;

  /**
   * Increment the hint-used counter for a problem's review session.
   * @param slug - The problem's unique slug identifier.
   */
  incrementReviewHints: (slug: string) => void;

  /**
   * Count how many problems the user has completed.
   * @returns The number of completed problems across all categories.
   */
  getCompletedCount: () => number;

  /**
   * Get the slugs of all completed problems.
   * @returns An array of problem slugs that have been marked as completed.
   */
  getCompletedSlugs: () => string[];

  /**
   * Start the solve timer for a problem. No-op if the timer is already
   * running or if the problem is already completed (unless in review mode).
   * @param slug - The problem's unique slug identifier.
   */
  startTimer: (slug: string) => void;

  /**
   * Stop the solve timer and accumulate elapsed time into solveDurationMs.
   * @param slug - The problem's unique slug identifier.
   */
  stopTimer: (slug: string) => void;

  /**
   * Enter review mode for a previously completed problem. Resets the
   * review-specific counters and starts a fresh timer.
   * @param slug - The problem's unique slug identifier.
   */
  startReview: (slug: string) => void;

  /**
   * Complete a review session. Calculates the SM-2 quality score from
   * review attempts/hints, schedules the next review, and clears review state.
   * @param slug - The problem's unique slug identifier.
   */
  completeReview: (slug: string) => void;

  /**
   * Cancel a review session without updating SRS scheduling.
   * Clears all review-specific state.
   * @param slug - The problem's unique slug identifier.
   */
  cancelReview: (slug: string) => void;

  /**
   * Get the list of problems that are due for SRS review, sorted by how
   * overdue they are (most overdue first), capped at DAILY_REVIEW_CAP.
   * @returns Array of due review info objects with slug and overdue days.
   */
  getDueReviews: () => DueReviewInfo[];

  /**
   * Get aggregate review statistics across all problems.
   * @returns Object with totalReviews (lifetime count) and dueCount (currently due).
   */
  getReviewStats: () => { totalReviews: number; dueCount: number };
}

/* ─── Default Progress Factory ──────────────────────────────────────────── */

/**
 * Creates a fresh ProblemProgress record with all fields at their initial
 * values. Used when a user first interacts with a problem (e.g., first
 * submission attempt, first hint reveal).
 *
 * @param slug - The problem's unique slug identifier.
 * @returns A new ProblemProgress with zero counters, no completion, and no SRS data.
 */
const createDefaultProgress = (slug: string): ProblemProgress => ({
  slug,
  completed: false,
  completedAt: null,
  attempts: 0,
  hintsUsed: 0,
  solveStartedAt: null,
  solveDurationMs: null,
  srs: null,
  reviewAttempts: 0,
  reviewHintsUsed: 0,
  isReviewing: false,
});

/* ─── Date & Streak Utilities ───────────────────────────────────────────── */

/**
 * Converts a Unix timestamp to a local-date string in "YYYY-MM-DD" format.
 * Used for streak comparison -- two timestamps on the same calendar day
 * (in the user's local timezone) produce the same string.
 *
 * @param ts - Unix timestamp in milliseconds.
 * @returns Date string like "2024-03-15".
 */
export function getDateString(ts: number): string {
  const d = new Date(ts);
  const year = d.getFullYear();
  const month = String(d.getMonth() + 1).padStart(2, '0');
  const day = String(d.getDate()).padStart(2, '0');
  return `${year}-${month}-${day}`;
}

/**
 * Calculates the updated streak data after a problem completion event.
 *
 * Streak logic:
 * - If the user already solved a problem today, the streak is unchanged.
 * - If the last solve was yesterday, the streak increments by 1.
 * - If the last solve was more than 1 day ago (or never), the streak resets to 1.
 * - The longest streak is always updated to the max of current and historical.
 *
 * @param streakData - The current streak state before this completion.
 * @returns Updated streak data with the new current streak, longest streak, and today's date.
 */
export function updateStreak(streakData: StreakData): StreakData {
  const today = getDateString(Date.now());
  const lastDate = streakData.lastSolveDate;

  if (lastDate === today) {
    return streakData;
  }

  const yesterdayDate = new Date();
  yesterdayDate.setDate(yesterdayDate.getDate() - 1);
  const yesterday = getDateString(yesterdayDate.getTime());
  let newStreak: number;

  if (lastDate === yesterday) {
    newStreak = streakData.currentStreak + 1;
  } else {
    newStreak = 1;
  }

  return {
    currentStreak: newStreak,
    longestStreak: Math.max(streakData.longestStreak, newStreak),
    lastSolveDate: today,
  };
}

/* ─── Increment Helper ──────────────────────────────────────────────────── */

/**
 * Union of numeric fields on ProblemProgress that can be incremented.
 * Used by the generic `incrementField` helper to avoid duplicating
 * the get-current-or-create-default + spread + set pattern.
 */
type NumericProgressField = 'attempts' | 'hintsUsed' | 'reviewAttempts' | 'reviewHintsUsed';

/**
 * Generic helper that increments a numeric field on a problem's progress record.
 * If no progress record exists for the slug, one is created with defaults first.
 *
 * This avoids duplicating the same boilerplate across incrementAttempts,
 * incrementHints, incrementReviewAttempts, and incrementReviewHints.
 *
 * @param get - Zustand getter for the current state.
 * @param set - Zustand setter for partial state updates.
 * @param slug - The problem's unique slug identifier.
 * @param field - The numeric field to increment by 1.
 */
function incrementField(
  get: () => ProgressState,
  set: (partial: Partial<ProgressState>) => void,
  slug: string,
  field: NumericProgressField
): void {
  const { progress } = get();
  const current = progress[slug] ?? createDefaultProgress(slug);
  set({
    progress: {
      ...progress,
      [slug]: { ...current, [field]: (current[field] as number) + 1 },
    },
  });
}

/* ─── Store Creation ────────────────────────────────────────────────────── */

export const useProgressStore = create<ProgressState>()(
  persist(
    (set, get) => ({
      progress: {},
      streakData: { currentStreak: 0, longestStreak: 0, lastSolveDate: null },

      getProgress: (slug: string) => {
        return get().progress[slug];
      },

      markCompleted: (slug: string) => {
        const { progress, streakData } = get();
        const current = progress[slug] ?? createDefaultProgress(slug);

        /**
         * Guard: if the problem is already completed and the user is NOT
         * in review mode, this is a no-op. This prevents overwriting the
         * original `completedAt` timestamp and inflating the streak by
         * counting the same problem's re-submission as a new solve.
         */
        if (current.completed && !current.isReviewing) return;

        /**
         * Stop the timer and calculate total duration. The timer may have
         * been paused and resumed multiple times, so we accumulate the
         * current elapsed segment onto any previously recorded duration.
         */
        let duration = current.solveDurationMs;
        if (current.solveStartedAt) {
          const elapsed = Date.now() - current.solveStartedAt;
          duration = (duration ?? 0) + elapsed;
        }

        const newStreak = updateStreak(streakData);

        /**
         * Initialize SRS scheduling on first completion. For already-completed
         * problems (review flow), the existing SRS data is preserved.
         * `createInitialSrs()` sets the first review for ~1 day out with
         * default ease factor.
         */
        const srs = current.srs ?? createInitialSrs();

        set({
          progress: {
            ...progress,
            [slug]: {
              ...current,
              completed: true,
              completedAt: current.completedAt ?? Date.now(),
              solveStartedAt: null,
              solveDurationMs: duration,
              srs,
              /**
               * Clear review state when marking completed. This handles the
               * case where a user completes a review -- we want to exit
               * review mode and reset review-specific counters so they
               * don't carry over to the next review session.
               */
              isReviewing: false,
              reviewAttempts: 0,
              reviewHintsUsed: 0,
            },
          },
          streakData: newStreak,
        });
      },

      incrementAttempts: (slug: string) => incrementField(get, set, slug, 'attempts'),
      incrementHints: (slug: string) => incrementField(get, set, slug, 'hintsUsed'),
      incrementReviewAttempts: (slug: string) => incrementField(get, set, slug, 'reviewAttempts'),
      incrementReviewHints: (slug: string) => incrementField(get, set, slug, 'reviewHintsUsed'),

      getCompletedCount: () => {
        const { progress } = get();
        return Object.values(progress).filter((p) => p.completed).length;
      },

      getCompletedSlugs: () => {
        const { progress } = get();
        return Object.values(progress)
          .filter((p) => p.completed)
          .map((p) => p.slug);
      },

      startTimer: (slug: string) => {
        const { progress } = get();
        const current = progress[slug] ?? createDefaultProgress(slug);

        /**
         * Guard conditions:
         * 1. If the problem is completed and NOT in review mode, don't re-time
         *    (the solve is already done).
         * 2. If `solveStartedAt` is already set, the timer is already running --
         *    don't restart it, which would lose previously accumulated time.
         * Exception: during review mode, we allow re-timing even if completed.
         */
        if ((current.completed && !current.isReviewing) || current.solveStartedAt !== null) return;
        set({
          progress: {
            ...progress,
            [slug]: {
              ...current,
              solveStartedAt: Date.now(),
            },
          },
        });
      },

      stopTimer: (slug: string) => {
        const { progress } = get();
        const current = progress[slug];
        if (!current?.solveStartedAt) return;
        const elapsed = Date.now() - current.solveStartedAt;
        set({
          progress: {
            ...progress,
            [slug]: {
              ...current,
              solveStartedAt: null,
              solveDurationMs: (current.solveDurationMs ?? 0) + elapsed,
            },
          },
        });
      },

      /* ── SRS / Review Actions ───────────────────────────────────────────── */

      startReview: (slug: string) => {
        const { progress } = get();
        const current = progress[slug] ?? createDefaultProgress(slug);

        /**
         * Enter review mode: set the isReviewing flag, reset review-specific
         * counters to zero (so this review session's performance is measured
         * independently), and start a fresh timer for the review attempt.
         */
        set({
          progress: {
            ...progress,
            [slug]: {
              ...current,
              isReviewing: true,
              reviewAttempts: 0,
              reviewHintsUsed: 0,
              solveStartedAt: Date.now(),
            },
          },
        });
      },

      completeReview: (slug: string) => {
        const { progress } = get();
        const current = progress[slug];

        /**
         * Guard: can only complete a review if SRS data exists. This prevents
         * errors if completeReview is called on a problem that was never
         * completed (and thus never had SRS initialized).
         */
        if (!current?.srs) return;

        /**
         * Derive the SM-2 quality score (0-5) from the user's review
         * performance. Fewer attempts and fewer hints yield higher quality,
         * which increases the interval before the next review.
         */
        const quality = deriveQuality(current.reviewAttempts, current.reviewHintsUsed);
        const newSrs = calculateNextReview(current.srs, quality);

        /**
         * Accumulate any elapsed timer time from the review session into
         * the total solveDurationMs. This ensures review time is tracked
         * alongside the original solve time.
         */
        let duration = current.solveDurationMs;
        if (current.solveStartedAt) {
          const elapsed = Date.now() - current.solveStartedAt;
          duration = (duration ?? 0) + elapsed;
        }

        set({
          progress: {
            ...progress,
            [slug]: {
              ...current,
              srs: newSrs,
              isReviewing: false,
              reviewAttempts: 0,
              reviewHintsUsed: 0,
              solveStartedAt: null,
              solveDurationMs: duration,
            },
          },
        });
      },

      cancelReview: (slug: string) => {
        const { progress } = get();
        const current = progress[slug];
        if (!current) return;

        /**
         * Cancel without updating SRS: the user chose to abandon this review,
         * so we don't penalize or reward them. We simply clear the review state
         * and stop the timer (without accumulating elapsed time, since the
         * review was not completed).
         */
        set({
          progress: {
            ...progress,
            [slug]: {
              ...current,
              isReviewing: false,
              reviewAttempts: 0,
              reviewHintsUsed: 0,
              solveStartedAt: null,
            },
          },
        });
      },

      getDueReviews: (): DueReviewInfo[] => {
        const { progress } = get();
        const due: DueReviewInfo[] = [];

        /**
         * Scan all progress records for problems with SRS data that are
         * currently due for review. Collect them with their overdue-days
         * count so we can prioritize the most overdue problems.
         */
        for (const p of Object.values(progress)) {
          if (p.srs && isReviewDue(p.srs)) {
            due.push({ slug: p.slug, overdueDays: daysOverdue(p.srs) });
          }
        }

        /**
         * Sort by most overdue first (descending overdueDays) and cap at
         * DAILY_REVIEW_CAP to avoid overwhelming the user. Problems that
         * are most overdue get priority because their memory decay is greatest.
         */
        due.sort((a, b) => b.overdueDays - a.overdueDays);
        return due.slice(0, DAILY_REVIEW_CAP);
      },

      getReviewStats: () => {
        const { progress } = get();
        let totalReviews = 0;
        let dueCount = 0;

        /**
         * Aggregate SRS statistics across all problems:
         * - totalReviews: lifetime count of completed reviews (sum of reviewCount)
         * - dueCount: number of problems currently due for review (no cap applied)
         */
        for (const p of Object.values(progress)) {
          if (p.srs) {
            totalReviews += p.srs.reviewCount;
            if (isReviewDue(p.srs)) dueCount++;
          }
        }
        return { totalReviews, dueCount };
      },
    }),

    /* ── Persistence Configuration ────────────────────────────────────────── */
    {
      /** localStorage key for this store's persisted state. */
      name: 'leetmethods-progress',

      /**
       * Schema version. Bump this when adding new fields to ProblemProgress
       * or StreakData and provide a corresponding migration below.
       * Current: v3 (added SRS fields).
       */
      version: 3,

      /**
       * Uses safeStorage, a wrapper around localStorage that catches
       * QuotaExceededError to prevent crashes when storage is full.
       */
      storage: safeStorage,

      /**
       * Schema migration function. Runs when the persisted version is older
       * than the current version. Each migration block is guarded by a
       * version check and upgrades the state shape incrementally.
       *
       * @param persisted - The raw persisted state object from localStorage.
       * @param version - The version number the persisted state was saved with.
       * @returns The migrated state compatible with the current schema.
       */
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      migrate: (persisted: unknown, version: number) => {
        const state = persisted as Record<string, unknown>;
        const progress = (state.progress ?? {}) as Record<string, Record<string, unknown>>;
        state.progress = progress;

        if (version < 2) {
          /**
           * Migration v1 -> v2: Add timer fields and streak data.
           * Problems saved under v1 had no timing or streak tracking.
           * We add null defaults so existing progress records are valid.
           */
          for (const slug of Object.keys(progress)) {
            if (progress[slug].solveStartedAt === undefined) {
              progress[slug].solveStartedAt = null;
            }
            if (progress[slug].solveDurationMs === undefined) {
              progress[slug].solveDurationMs = null;
            }
          }
          if (!state.streakData) {
            state.streakData = { currentStreak: 0, longestStreak: 0, lastSolveDate: null };
          }
        }

        if (version < 3) {
          /**
           * Migration v2 -> v3: Add SRS (Spaced Repetition System) fields.
           * For problems that are already completed, we initialize SRS with
           * staggered review dates using `createMigratedSrs(index)`. This
           * spreads first reviews over ~14 days so the user isn't hit with
           * all reviews at once after upgrading. Incomplete problems get
           * null SRS (it will be initialized when they're first completed).
           */
          let completedIndex = 0;
          for (const slug of Object.keys(progress)) {
            if (progress[slug].srs === undefined) {
              if (progress[slug].completed) {
                progress[slug].srs = createMigratedSrs(completedIndex++);
              } else {
                progress[slug].srs = null;
              }
            }
            if (progress[slug].reviewAttempts === undefined) {
              progress[slug].reviewAttempts = 0;
            }
            if (progress[slug].reviewHintsUsed === undefined) {
              progress[slug].reviewHintsUsed = 0;
            }
            if (progress[slug].isReviewing === undefined) {
              progress[slug].isReviewing = false;
            }
          }
        }

        return state as unknown as ProgressState;
      },
    }
  )
);
