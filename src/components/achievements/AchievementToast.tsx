/**
 * @module AchievementToast
 *
 * Animated toast notification that appears when the user unlocks an achievement.
 *
 * This component monitors the `pendingToasts` queue in the `achievementStore`
 * and displays one toast at a time with a slide-up/fade-in animation. Each
 * toast auto-dismisses after 4 seconds with a matching fade-out animation.
 *
 * Toast lifecycle:
 *   1. A new achievement ID appears in `pendingToasts`
 *   2. The component picks the first pending toast and shows it (fade in)
 *   3. After 4 seconds, the toast fades out (300ms transition)
 *   4. After the fade-out completes, the toast is cleared from the queue
 *   5. If more toasts are pending, the cycle repeats for the next one
 *
 * Design decisions:
 *   - Only one toast is shown at a time to avoid visual clutter. Multiple
 *     unlocks are queued and shown sequentially.
 *   - The component uses a ref (`innerTimerRef`) for the fade-out cleanup
 *     timer to ensure proper cleanup if the component unmounts mid-animation.
 *   - The `currentToast` state prevents re-triggering the same toast if
 *     `pendingToasts` changes while one is already being displayed.
 *   - The toast is positioned fixed at the bottom-right (z-200) to float
 *     above all other UI elements including modals.
 *   - The golden border and "Achievement Unlocked!" header create a
 *     celebratory visual that matches the golden theme of the AchievementGrid.
 */
'use client';

import { useEffect, useRef, useState } from 'react';
import { useAchievementStore } from '@/store/achievementStore';
import { achievements } from '@/lib/achievements';

/**
 * Renders an animated achievement toast notification.
 *
 * Monitors the pending toast queue and displays achievements one at a time
 * with timed auto-dismiss and fade animations.
 *
 * @returns A fixed-position toast element, or null if no toast is active.
 */
export function AchievementToast() {
  /** Queue of achievement IDs waiting to be displayed */
  const pendingToasts = useAchievementStore((s) => s.pendingToasts);
  /** Function to remove a toast from the pending queue after it has been shown */
  const clearToast = useAchievementStore((s) => s.clearToast);

  /** The achievement ID currently being displayed, or null if idle */
  const [currentToast, setCurrentToast] = useState<string | null>(null);
  /** Controls the CSS opacity/transform transition for fade in/out */
  const [visible, setVisible] = useState(false);

  /**
   * Ref to the inner timer that fires after the fade-out animation completes.
   * Stored as a ref (not state) to allow cleanup in the effect's destructor
   * without triggering re-renders. Uses ReturnType<typeof setTimeout> for
   * environment-agnostic timer ID typing.
   */
  const innerTimerRef = useRef<ReturnType<typeof setTimeout> | null>(null);

  /**
   * Main toast lifecycle effect.
   *
   * When there are pending toasts and no toast is currently showing:
   *   1. Pick the first pending toast
   *   2. Show it with fade-in
   *   3. After 4s, start fade-out
   *   4. After 300ms fade-out, clear the toast and reset state
   *
   * Cleanup ensures both timers are cleared if the component unmounts
   * or the effect re-runs while a toast is in progress.
   */
  useEffect(() => {
    if (pendingToasts.length > 0 && !currentToast) {
      const next = pendingToasts[0];
      setCurrentToast(next);
      setVisible(true);

      /* Auto-dismiss timer: start fade-out after 4 seconds of visibility */
      const timer = setTimeout(() => {
        setVisible(false);
        /* Inner timer: wait for the 300ms CSS fade-out transition to complete,
           then actually remove the toast from the queue and reset state */
        innerTimerRef.current = setTimeout(() => {
          innerTimerRef.current = null;
          clearToast(next);
          setCurrentToast(null);
        }, 300);
      }, 4000);

      /* Cleanup: cancel both the auto-dismiss timer and any in-progress
         fade-out timer to prevent state updates after unmount */
      return () => {
        clearTimeout(timer);
        if (innerTimerRef.current !== null) {
          clearTimeout(innerTimerRef.current);
          innerTimerRef.current = null;
        }
      };
    }
  }, [pendingToasts, currentToast, clearToast]);

  /* Don't render anything if no toast is active */
  if (!currentToast) return null;

  /* Look up the achievement definition to get the icon, title, and description */
  const achievement = achievements.find((a) => a.id === currentToast);
  if (!achievement) return null;

  return (
    <div
      className={`fixed bottom-6 right-6 z-[200] transition-all duration-300 ${
        visible ? 'opacity-100 translate-y-0' : 'opacity-0 translate-y-4'
      }`}
    >
      {/* Toast card with golden border to match the achievement theme */}
      <div className="bg-background border-2 border-yellow-400 dark:border-yellow-500 rounded-lg shadow-lg px-4 py-3 flex items-center gap-3 min-w-[280px]">
        {/* Achievement icon (emoji) */}
        <span className="text-2xl">{achievement.icon}</span>
        <div>
          {/* "Achievement Unlocked!" label in uppercase golden text */}
          <div className="text-xs font-medium text-yellow-600 dark:text-yellow-400 uppercase tracking-wider">
            Achievement Unlocked!
          </div>
          {/* Achievement title and description */}
          <div className="font-semibold">{achievement.title}</div>
          <div className="text-xs text-muted-foreground">{achievement.description}</div>
        </div>
      </div>
    </div>
  );
}
