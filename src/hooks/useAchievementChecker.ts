/**
 * @module useAchievementChecker
 *
 * React hook that provides a stable callback for checking and unlocking
 * achievements after a problem is completed or a review is finished.
 *
 * This hook bridges three systems:
 * 1. **progressStore** -- reads the current progress and streak data to
 *    evaluate achievement conditions (e.g., "completed 10 problems",
 *    "maintained a 7-day streak").
 * 2. **achievementStore** -- reads the set of already-unlocked achievements
 *    to avoid re-evaluation, and calls `unlock()` for newly earned ones.
 * 3. **checkAchievements()** (in `src/lib/achievements.ts`) -- the pure
 *    function that evaluates all achievement rules against the current
 *    state and returns the list of newly qualifying achievement IDs.
 *
 * Why `getState()` instead of hooks:
 * The `checkAndUnlock` callback uses `useProgressStore.getState()` and
 * `useAchievementStore.getState()` instead of subscribing via hooks.
 * This is intentional -- the callback is typically called immediately after
 * `markCompleted()`, and React may not have flushed the Zustand state update
 * into hook subscriptions yet (stale closure). Reading directly from
 * `getState()` always returns the latest committed store state, avoiding
 * a subtle timing bug where newly completed problems are missed.
 *
 * Usage:
 * ```tsx
 * const { checkAndUnlock } = useAchievementChecker(allProblems);
 *
 * const handleSubmitSuccess = () => {
 *   progressStore.markCompleted(slug);
 *   checkAndUnlock(); // Reads latest state, unlocks any new achievements
 * };
 * ```
 */

import { useCallback } from 'react';
import { useProgressStore } from '@/store/progressStore';
import { useAchievementStore } from '@/store/achievementStore';
import { checkAchievements } from '@/lib/achievements';
import type { ProblemSummary } from '@/lib/problems/types';

/**
 * Hook that returns a `checkAndUnlock` callback for evaluating and
 * unlocking achievements based on the current progress state.
 *
 * @param problems - The full list of problem summaries (built-in + custom).
 *   Passed to `checkAchievements()` so it can evaluate conditions like
 *   "completed all problems in category X" or "completed N% of all problems".
 *
 * @returns An object containing:
 *   - `checkAndUnlock`: A stable callback that reads the latest progress
 *     and achievement state, evaluates all achievement rules, and unlocks
 *     any newly qualifying achievements (which enqueues their toast
 *     notifications in the achievement store).
 */
export function useAchievementChecker(problems: ProblemSummary[]) {
  const checkAndUnlock = useCallback(() => {
    /**
     * Read the latest state directly from the stores rather than from
     * hook subscriptions. This avoids stale closures when checkAndUnlock
     * is called synchronously after a state mutation (e.g., markCompleted).
     */
    const { progress, streakData } = useProgressStore.getState();
    const { getUnlockedIds, unlock } = useAchievementStore.getState();
    const unlockedIds = getUnlockedIds();

    /**
     * checkAchievements is a pure function that evaluates all achievement
     * rules and returns only the IDs that are newly qualifying (not already
     * in unlockedIds). This keeps the rule engine side-effect-free.
     */
    const newlyUnlocked = checkAchievements(progress, problems, streakData, unlockedIds);

    /**
     * Unlock each newly qualifying achievement. The store's unlock()
     * method is idempotent (checks for existing unlock before adding),
     * but we've already filtered to only new ones via checkAchievements.
     */
    for (const id of newlyUnlocked) {
      unlock(id);
    }
  }, [problems]);

  return { checkAndUnlock };
}
