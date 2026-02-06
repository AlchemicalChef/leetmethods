'use client';

import { useEffect, useRef, useState } from 'react';
import { useAchievementStore } from '@/store/achievementStore';
import { achievements } from '@/lib/achievements';

export function AchievementToast() {
  const pendingToasts = useAchievementStore((s) => s.pendingToasts);
  const clearToast = useAchievementStore((s) => s.clearToast);
  const [currentToast, setCurrentToast] = useState<string | null>(null);
  const [visible, setVisible] = useState(false);
  const innerTimerRef = useRef<ReturnType<typeof setTimeout> | null>(null);

  useEffect(() => {
    if (pendingToasts.length > 0 && !currentToast) {
      const next = pendingToasts[0];
      setCurrentToast(next);
      setVisible(true);

      const timer = setTimeout(() => {
        setVisible(false);
        innerTimerRef.current = setTimeout(() => {
          innerTimerRef.current = null;
          clearToast(next);
          setCurrentToast(null);
        }, 300);
      }, 4000);

      return () => {
        clearTimeout(timer);
        if (innerTimerRef.current !== null) {
          clearTimeout(innerTimerRef.current);
          innerTimerRef.current = null;
        }
      };
    }
  }, [pendingToasts, currentToast, clearToast]);

  if (!currentToast) return null;

  const achievement = achievements.find((a) => a.id === currentToast);
  if (!achievement) return null;

  return (
    <div
      className={`fixed bottom-6 right-6 z-[200] transition-all duration-300 ${
        visible ? 'opacity-100 translate-y-0' : 'opacity-0 translate-y-4'
      }`}
    >
      <div className="bg-background border-2 border-yellow-400 dark:border-yellow-500 rounded-lg shadow-lg px-4 py-3 flex items-center gap-3 min-w-[280px]">
        <span className="text-2xl">{achievement.icon}</span>
        <div>
          <div className="text-xs font-medium text-yellow-600 dark:text-yellow-400 uppercase tracking-wider">
            Achievement Unlocked!
          </div>
          <div className="font-semibold">{achievement.title}</div>
          <div className="text-xs text-muted-foreground">{achievement.description}</div>
        </div>
      </div>
    </div>
  );
}
