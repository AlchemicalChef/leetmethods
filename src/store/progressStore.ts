import { create } from 'zustand';
import { persist } from 'zustand/middleware';
import { safeStorage } from '@/lib/safe-storage';
import { createInitialSrs, createMigratedSrs, calculateNextReview, deriveQuality, isReviewDue, daysOverdue } from '@/lib/srs';
import type { ProblemProgress, StreakData, DueReviewInfo } from '@/lib/types/progress';

export type { ProblemProgress, StreakData, DueReviewInfo };

const DAILY_REVIEW_CAP = 5;

interface ProgressState {
  progress: Record<string, ProblemProgress>;
  streakData: StreakData;

  getProgress: (slug: string) => ProblemProgress | undefined;
  markCompleted: (slug: string) => void;
  incrementAttempts: (slug: string) => void;
  incrementHints: (slug: string) => void;
  incrementReviewAttempts: (slug: string) => void;
  incrementReviewHints: (slug: string) => void;
  getCompletedCount: () => number;
  getCompletedSlugs: () => string[];
  startTimer: (slug: string) => void;
  stopTimer: (slug: string) => void;
  // SRS/Review actions
  startReview: (slug: string) => void;
  completeReview: (slug: string) => void;
  cancelReview: (slug: string) => void;
  getDueReviews: () => DueReviewInfo[];
  getReviewStats: () => { totalReviews: number; dueCount: number };
}

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

export function getDateString(ts: number): string {
  const d = new Date(ts);
  const year = d.getFullYear();
  const month = String(d.getMonth() + 1).padStart(2, '0');
  const day = String(d.getDate()).padStart(2, '0');
  return `${year}-${month}-${day}`;
}

export function updateStreak(streakData: StreakData): StreakData {
  const today = getDateString(Date.now());
  const lastDate = streakData.lastSolveDate;

  if (lastDate === today) {
    return streakData; // Already solved today
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

type NumericProgressField = 'attempts' | 'hintsUsed' | 'reviewAttempts' | 'reviewHintsUsed';

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

export const useProgressStore = create<ProgressState>()(
  persist(
    (set, get) => ({
      progress: {},
      streakData: { currentStreak: 0, longestStreak: 0, lastSolveDate: null },

      getProgress: (slug: string) => {
        return get().progress[slug];
      },

      // FIX #8: Don't increment attempts here - it's already done in handleSubmit
      markCompleted: (slug: string) => {
        const { progress, streakData } = get();
        const current = progress[slug] ?? createDefaultProgress(slug);

        // Stop timer and calculate duration
        let duration = current.solveDurationMs;
        if (current.solveStartedAt) {
          const elapsed = Date.now() - current.solveStartedAt;
          duration = (duration ?? 0) + elapsed;
        }

        const newStreak = updateStreak(streakData);

        // Initialize SRS on first completion
        const srs = current.srs ?? createInitialSrs();

        set({
          progress: {
            ...progress,
            [slug]: {
              ...current,
              completed: true,
              completedAt: Date.now(),
              solveStartedAt: null,
              solveDurationMs: duration,
              srs,
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
        // Allow re-timing during review even if completed
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

      // SRS / Review actions
      startReview: (slug: string) => {
        const { progress } = get();
        const current = progress[slug] ?? createDefaultProgress(slug);
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
        if (!current?.srs) return;

        const quality = deriveQuality(current.reviewAttempts, current.reviewHintsUsed);
        const newSrs = calculateNextReview(current.srs, quality);

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
            },
          },
        });
      },

      cancelReview: (slug: string) => {
        const { progress } = get();
        const current = progress[slug];
        if (!current) return;
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
        for (const p of Object.values(progress)) {
          if (p.srs && isReviewDue(p.srs)) {
            due.push({ slug: p.slug, overdueDays: daysOverdue(p.srs) });
          }
        }
        due.sort((a, b) => b.overdueDays - a.overdueDays);
        return due.slice(0, DAILY_REVIEW_CAP);
      },

      getReviewStats: () => {
        const { progress } = get();
        let totalReviews = 0;
        let dueCount = 0;
        for (const p of Object.values(progress)) {
          if (p.srs) {
            totalReviews += p.srs.reviewCount;
            if (isReviewDue(p.srs)) dueCount++;
          }
        }
        return { totalReviews, dueCount };
      },
    }),
    {
      name: 'leetmethods-progress',
      version: 3,
      storage: safeStorage,
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      migrate: (persisted: unknown, version: number) => {
        const state = persisted as Record<string, unknown>;
        const progress = (state.progress ?? {}) as Record<string, Record<string, unknown>>;

        if (version < 2) {
          // Migrate v1 -> v2: add timer fields
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
          // Migrate v2 -> v3: add SRS fields
          let completedIndex = 0;
          for (const slug of Object.keys(progress)) {
            if (progress[slug].srs === undefined) {
              // Initialize SRS for already-completed problems, staggered over 14 days
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
