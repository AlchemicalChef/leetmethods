import { create } from 'zustand';
import { persist } from 'zustand/middleware';
import { safeStorage } from '@/lib/safe-storage';

interface AchievementState {
  unlockedAchievements: Record<string, number>; // id -> unlockedAt timestamp
  pendingToasts: string[]; // achievement IDs to show

  unlock: (id: string) => void;
  clearToast: (id: string) => void;
  isUnlocked: (id: string) => boolean;
  getUnlockedIds: () => Set<string>;
}

export const useAchievementStore = create<AchievementState>()(
  persist(
    (set, get) => ({
      unlockedAchievements: {},
      pendingToasts: [],

      unlock: (id: string) => {
        const { unlockedAchievements, pendingToasts } = get();
        if (unlockedAchievements[id]) return;
        set({
          unlockedAchievements: {
            ...unlockedAchievements,
            [id]: Date.now(),
          },
          pendingToasts: [...pendingToasts, id],
        });
      },

      clearToast: (id: string) => {
        set((state) => ({
          pendingToasts: state.pendingToasts.filter((t) => t !== id),
        }));
      },

      isUnlocked: (id: string) => {
        return !!get().unlockedAchievements[id];
      },

      getUnlockedIds: () => {
        return new Set(Object.keys(get().unlockedAchievements));
      },
    }),
    {
      name: 'leetmethods-achievements',
      storage: safeStorage,
      partialize: (state) => ({
        unlockedAchievements: state.unlockedAchievements,
      }),
    }
  )
);
