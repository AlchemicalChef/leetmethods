/**
 * @module achievementStore
 *
 * Persisted Zustand store for the achievement / badge system.
 *
 * Achievements are unlocked based on user milestones (e.g., completing N
 * problems, maintaining a streak, solving within a time limit). The actual
 * achievement-checking logic lives in `src/lib/achievements.ts` and is
 * triggered by the `useAchievementChecker` hook after problem completion.
 * This store is purely responsible for:
 *
 * 1. Recording which achievements have been unlocked (and when).
 * 2. Managing a queue of pending toast notifications so the UI can display
 *    celebratory popups for newly unlocked achievements.
 *
 * Persistence:
 * - Both `unlockedAchievements` and `pendingToasts` are persisted to
 *   localStorage via `safeStorage`. Persisting `pendingToasts` ensures
 *   that if the user closes the browser before seeing a toast, it will
 *   still be shown on the next visit.
 *
 * Design notes:
 * - `unlockedAchievements` is a Record<string, number> mapping achievement
 *   IDs to their unlock timestamp. The timestamp enables "unlocked at"
 *   display in the UI and chronological sorting.
 * - `pendingToasts` is a simple string array of achievement IDs. Toasts
 *   are consumed (cleared) by the UI component after display.
 * - The `unlock()` method is idempotent: calling it with an already-unlocked
 *   achievement ID is a no-op, preventing duplicate toasts.
 */

import { create } from 'zustand';
import { persist } from 'zustand/middleware';
import { safeStorage } from '@/lib/safe-storage';

/* ─── Store Interface ───────────────────────────────────────────────────── */

interface AchievementState {
  /**
   * Map from achievement ID to the Unix timestamp (ms) when it was unlocked.
   * An achievement is considered unlocked if and only if it has an entry here.
   */
  unlockedAchievements: Record<string, number>;

  /**
   * Queue of achievement IDs whose toast notifications have not yet been
   * shown to the user. The UI consumes these by calling `clearToast()`
   * after displaying each one.
   */
  pendingToasts: string[];

  /**
   * Unlock an achievement and enqueue its toast notification.
   * Idempotent: if the achievement is already unlocked, this is a no-op
   * (no duplicate toast is enqueued).
   *
   * @param id - The unique achievement identifier (e.g., "first-proof", "streak-7").
   */
  unlock: (id: string) => void;

  /**
   * Remove an achievement ID from the pending toasts queue after the UI
   * has displayed the toast. Filters out all occurrences of the ID.
   *
   * @param id - The achievement identifier to remove from the toast queue.
   */
  clearToast: (id: string) => void;

  /**
   * Check whether a specific achievement has been unlocked.
   *
   * @param id - The achievement identifier to check.
   * @returns True if the achievement has been unlocked, false otherwise.
   */
  isUnlocked: (id: string) => boolean;

  /**
   * Get the full set of unlocked achievement IDs. Returns a Set for
   * efficient O(1) membership testing, which is useful when the
   * achievement checker needs to skip already-unlocked achievements.
   *
   * @returns A Set containing all unlocked achievement IDs.
   */
  getUnlockedIds: () => Set<string>;
}

/* ─── Store Creation ────────────────────────────────────────────────────── */

export const useAchievementStore = create<AchievementState>()(
  persist(
    (set, get) => ({
      unlockedAchievements: {},
      pendingToasts: [],

      unlock: (id: string) => {
        const { unlockedAchievements, pendingToasts } = get();

        /**
         * Idempotency guard: if the achievement already has a timestamp in
         * the map, it was previously unlocked. Return early to avoid adding
         * a duplicate toast notification.
         */
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
        /**
         * Double-bang coercion: `unlockedAchievements[id]` is a timestamp
         * (truthy number) or undefined. `!!` converts to a clean boolean.
         */
        return !!get().unlockedAchievements[id];
      },

      getUnlockedIds: () => {
        return new Set(Object.keys(get().unlockedAchievements));
      },
    }),

    /* ── Persistence Configuration ──────────────────────────────────────── */
    {
      /** localStorage key for this store's persisted state. */
      name: 'leetmethods-achievements',

      /**
       * Uses safeStorage, a wrapper around localStorage that catches
       * QuotaExceededError to prevent crashes when storage is full.
       */
      storage: safeStorage,

      /**
       * Persist both the unlock map and pending toasts. Persisting toasts
       * ensures that newly-unlocked achievement notifications survive page
       * reloads -- the user will see them on their next visit even if they
       * closed the tab before the toast appeared.
       */
      partialize: (state) => ({
        unlockedAchievements: state.unlockedAchievements,
        pendingToasts: state.pendingToasts,
      }),
    }
  )
);
