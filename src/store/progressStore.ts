import { create } from 'zustand';
import { persist } from 'zustand/middleware';

export interface ProblemProgress {
  slug: string;
  completed: boolean;
  completedAt: number | null;
  attempts: number;
  hintsUsed: number;
}

interface ProgressState {
  progress: Record<string, ProblemProgress>;

  getProgress: (slug: string) => ProblemProgress | undefined;
  markCompleted: (slug: string) => void;
  incrementAttempts: (slug: string) => void;
  incrementHints: (slug: string) => void;
  getCompletedCount: () => number;
  getCompletedSlugs: () => string[];
}

const createDefaultProgress = (slug: string): ProblemProgress => ({
  slug,
  completed: false,
  completedAt: null,
  attempts: 0,
  hintsUsed: 0,
});

export const useProgressStore = create<ProgressState>()(
  persist(
    (set, get) => ({
      progress: {},

      getProgress: (slug: string) => {
        return get().progress[slug];
      },

      // FIX #8: Don't increment attempts here - it's already done in handleSubmit
      markCompleted: (slug: string) => {
        const { progress } = get();
        const current = progress[slug] ?? createDefaultProgress(slug);
        set({
          progress: {
            ...progress,
            [slug]: {
              ...current,
              completed: true,
              completedAt: Date.now(),
              // Removed: attempts: current.attempts + 1
            },
          },
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
    }),
    {
      name: 'leetmethods-progress',
    }
  )
);
