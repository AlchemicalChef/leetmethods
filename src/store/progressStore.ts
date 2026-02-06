import { create } from 'zustand';
import { persist } from 'zustand/middleware';

export interface ProblemProgress {
  slug: string;
  completed: boolean;
  completedAt: number | null;
  attempts: number;
  hintsUsed: number;
  solveStartedAt: number | null;
  solveDurationMs: number | null;
}

export interface StreakData {
  currentStreak: number;
  longestStreak: number;
  lastSolveDate: string | null; // ISO date string YYYY-MM-DD
}

interface ProgressState {
  progress: Record<string, ProblemProgress>;
  streakData: StreakData;

  getProgress: (slug: string) => ProblemProgress | undefined;
  markCompleted: (slug: string) => void;
  incrementAttempts: (slug: string) => void;
  incrementHints: (slug: string) => void;
  getCompletedCount: () => number;
  getCompletedSlugs: () => string[];
  startTimer: (slug: string) => void;
  stopTimer: (slug: string) => void;
}

const createDefaultProgress = (slug: string): ProblemProgress => ({
  slug,
  completed: false,
  completedAt: null,
  attempts: 0,
  hintsUsed: 0,
  solveStartedAt: null,
  solveDurationMs: null,
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

        set({
          progress: {
            ...progress,
            [slug]: {
              ...current,
              completed: true,
              completedAt: Date.now(),
              solveStartedAt: null,
              solveDurationMs: duration,
            },
          },
          streakData: newStreak,
        });
      },

      incrementAttempts: (slug: string) => {
        const { progress } = get();
        const current = progress[slug] ?? createDefaultProgress(slug);
        set({
          progress: {
            ...progress,
            [slug]: {
              ...current,
              attempts: current.attempts + 1,
            },
          },
        });
      },

      incrementHints: (slug: string) => {
        const { progress } = get();
        const current = progress[slug] ?? createDefaultProgress(slug);
        set({
          progress: {
            ...progress,
            [slug]: {
              ...current,
              hintsUsed: current.hintsUsed + 1,
            },
          },
        });
      },

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
        if (current.completed || current.solveStartedAt !== null) return; // Don't restart if completed or already running
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
    }),
    {
      name: 'leetmethods-progress',
      version: 2,
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      migrate: (persisted: unknown, version: number) => {
        if (version < 2) {
          // Migrate v1 -> v2: add new fields to existing progress entries
          const state = persisted as Record<string, unknown>;
          const progress = (state.progress ?? {}) as Record<string, Record<string, unknown>>;
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
          return state as unknown as ProgressState;
        }
        return persisted as unknown as ProgressState;
      },
    }
  )
);
