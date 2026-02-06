import { useCallback } from 'react';
import { useProgressStore } from '@/store/progressStore';
import { useAchievementStore } from '@/store/achievementStore';
import { checkAchievements } from '@/lib/achievements';
import type { ProblemSummary } from '@/lib/problems/types';

export function useAchievementChecker(problems: ProblemSummary[]) {
  // Use getState() directly to always read the latest store state,
  // avoiding stale closures when called immediately after markCompleted()
  const checkAndUnlock = useCallback(() => {
    const { progress, streakData } = useProgressStore.getState();
    const { getUnlockedIds, unlock } = useAchievementStore.getState();
    const unlockedIds = getUnlockedIds();
    const newlyUnlocked = checkAchievements(progress, problems, streakData, unlockedIds);
    for (const id of newlyUnlocked) {
      unlock(id);
    }
  }, [problems]);

  return { checkAndUnlock };
}
