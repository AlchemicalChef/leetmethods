/**
 * @module AchievementGrid
 *
 * Renders a responsive grid of all achievement cards with lock/unlock styling.
 *
 * This component displays every achievement defined in the app, visually
 * distinguishing between unlocked and locked achievements. Unlocked
 * achievements have a golden border and warm background tint, while locked
 * achievements are dimmed with reduced opacity and grayscale filtering.
 *
 * The achievements list comes from `src/lib/achievements.ts` (a static
 * array of achievement definitions), and the unlock status comes from the
 * `achievementStore` Zustand store which persists to localStorage.
 *
 * Design decisions:
 *   - All achievements are always shown (not just unlocked ones) so users
 *     can see what they have yet to earn, creating a sense of progression.
 *   - The grid uses a responsive column layout: 2 columns on mobile,
 *     3 on medium, and 4 on large screens.
 *   - The unlock check uses `!!` to coerce the potentially undefined
 *     value from the `unlockedAchievements` record into a boolean.
 */
'use client';

import { Card } from '@/components/ui/card';
import { useAchievementStore } from '@/store/achievementStore';
import { achievements } from '@/lib/achievements';

/**
 * Renders a grid of all achievements with visual indicators for
 * locked vs. unlocked status.
 *
 * @returns A responsive grid of achievement cards.
 */
export function AchievementGrid() {
  /** Map of achievement ID to unlock timestamp (or undefined if locked) */
  const { unlockedAchievements } = useAchievementStore();

  return (
    <div className="grid grid-cols-2 md:grid-cols-3 lg:grid-cols-4 gap-3">
      {achievements.map((ach) => {
        /** Boolean indicating whether this achievement has been unlocked */
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
            {/* Achievement icon (emoji) displayed prominently */}
            <div className="text-2xl mb-1">{ach.icon}</div>
            {/* Achievement title */}
            <div className="text-sm font-medium">{ach.title}</div>
            {/* Achievement description -- brief text explaining the unlock condition */}
            <div className="text-xs text-muted-foreground mt-1">{ach.description}</div>
          </Card>
        );
      })}
    </div>
  );
}
