'use client';

import { Card } from '@/components/ui/card';
import { useAchievementStore } from '@/store/achievementStore';
import { achievements } from '@/lib/achievements';

export function AchievementGrid() {
  const { unlockedAchievements } = useAchievementStore();

  return (
    <div className="grid grid-cols-2 md:grid-cols-3 lg:grid-cols-4 gap-3">
      {achievements.map((ach) => {
        const unlocked = !!unlockedAchievements[ach.id];
        return (
          <Card
            key={ach.id}
            className={`p-3 text-center transition-all ${
              unlocked
                ? 'border-yellow-400 dark:border-yellow-500 bg-yellow-50/50 dark:bg-yellow-950/20'
                : 'opacity-50 grayscale'
            }`}
          >
            <div className="text-2xl mb-1">{ach.icon}</div>
            <div className="text-sm font-medium">{ach.title}</div>
            <div className="text-xs text-muted-foreground mt-1">{ach.description}</div>
          </Card>
        );
      })}
    </div>
  );
}
