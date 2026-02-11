/**
 * @module StatsOverview
 *
 * Main dashboard component for the Stats page (`/stats`).
 *
 * This component provides a comprehensive view of the user's progress
 * and performance, organized into several sections:
 *   1. **Summary stat cards** -- Solved count, completion %, streak, avg time
 *   2. **Category progress** -- Per-category progress bars with color coding
 *   3. **Difficulty breakdown** -- Easy/Medium/Hard solved counts
 *   4. **Activity summary** -- Total attempts, hints used, total time, streak
 *   5. **Due for Review** -- SRS-scheduled problems that need review
 *   6. **Achievements** -- Grid of all achievements with unlock status
 *
 * All statistics are computed by `computeStats()` from `src/lib/stats.ts`,
 * which derives everything from the `progressStore` data and the available
 * problems list. The computation is memoized with `useMemo` to avoid
 * recalculating on every render.
 *
 * Design decisions:
 *   - Statistics are computed client-side from localStorage-backed stores,
 *     so this component must be a client component.
 *   - The `problems` prop is passed from the page-level component which
 *     loads problems synchronously via static imports.
 *   - Color constants for categories come from `ui-constants` to maintain
 *     consistent coloring across the Stats and Learn pages.
 *   - Helper sub-components (StatCard, DifficultyCard) are defined in the
 *     same file since they are only used here and are simple presentational
 *     components.
 */
'use client';

import { useMemo } from 'react';
import { Card } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import { Trophy, Target, Flame, Clock } from 'lucide-react';
import { useProgressStore } from '@/store/progressStore';
import { computeStats, formatDuration } from '@/lib/stats';
import type { ProblemSummary } from '@/lib/problems/types';
import { CATEGORY_LABELS, CATEGORY_COLORS } from '@/lib/ui-constants';
import { AchievementGrid } from '@/components/achievements/AchievementGrid';
import { ReviewSection } from '@/components/stats/ReviewSection';

/**
 * Props for the StatsOverview component.
 *
 * @property problems - Complete list of all problem summaries, used to
 *   compute per-category and per-difficulty statistics.
 */
interface StatsOverviewProps {
  problems: ProblemSummary[];
}

/**
 * Renders the full Stats page dashboard with summary cards, progress bars,
 * difficulty breakdown, activity summary, review section, and achievements.
 *
 * @param props - Component props containing all available problem summaries.
 * @returns The complete stats dashboard UI.
 */
export function StatsOverview({ problems }: StatsOverviewProps) {
  /** Subscribe to the progress record for per-problem completion data */
  const progress = useProgressStore((s) => s.progress);
  /** Subscribe to streak data for current/longest streak calculations */
  const streakData = useProgressStore((s) => s.streakData);

  /**
   * Memoized stats computation. Depends on progress, problems, and streakData.
   * The `computeStats` function aggregates all progress data into a single
   * stats object with counts, percentages, category breakdowns, etc.
   */
  const stats = useMemo(
    () => computeStats(progress, problems, streakData),
    [progress, problems, streakData]
  );

  return (
    <div className="space-y-8">
      {/* ================================================================
       * Section 1: Summary Stat Cards
       * Four key metrics displayed in a responsive 2x2 / 4x1 grid.
       * ================================================================ */}
      <div className="grid grid-cols-2 md:grid-cols-4 gap-4">
        <StatCard
          icon={<Trophy className="h-5 w-5 text-yellow-500" />}
          label="Solved"
          value={`${stats.solvedCount}/${stats.totalProblems}`}
        />
        <StatCard
          icon={<Target className="h-5 w-5 text-blue-500" />}
          label="Complete"
          value={`${stats.completionPercent}%`}
        />
        <StatCard
          icon={<Flame className="h-5 w-5 text-orange-500" />}
          label="Streak"
          value={`${stats.currentStreak} day${stats.currentStreak !== 1 ? 's' : ''}`}
          subtitle={stats.longestStreak > 0 ? `Best: ${stats.longestStreak}` : undefined}
        />
        <StatCard
          icon={<Clock className="h-5 w-5 text-green-500" />}
          label="Avg. Time"
          value={formatDuration(stats.averageTimeMs)}
        />
      </div>

      {/* ================================================================
       * Section 2: Category Progress
       * Progress bars for each problem category, color-coded using the
       * centralized CATEGORY_COLORS map from ui-constants.
       * ================================================================ */}
      <div>
        <h3 className="text-lg font-semibold mb-4">Progress by Category</h3>
        <div className="space-y-3">
          {stats.categoryStats.map((cat) => (
            <div key={cat.category}>
              <div className="flex items-center justify-between mb-1">
                <span className="text-sm font-medium">{CATEGORY_LABELS[cat.category]}</span>
                <span className="text-sm text-muted-foreground">
                  {cat.solved}/{cat.total}
                </span>
              </div>
              {/* Progress bar with category-specific color class */}
              <div className="h-2 bg-muted rounded-full overflow-hidden">
                <div
                  className={`h-full rounded-full transition-all duration-500 ${CATEGORY_COLORS[cat.category]}`}
                  style={{ width: `${cat.percent}%` }}
                />
              </div>
            </div>
          ))}
        </div>
      </div>

      {/* ================================================================
       * Section 3: Difficulty Breakdown
       * Three cards showing solved/total for Easy, Medium, and Hard problems.
       * Color coding uses green/yellow/red to match conventional difficulty
       * indicators.
       * ================================================================ */}
      <div>
        <h3 className="text-lg font-semibold mb-4">Difficulty Breakdown</h3>
        <div className="grid grid-cols-3 gap-4">
          <DifficultyCard
            label="Easy"
            solved={stats.difficultyStats.easy}
            total={stats.difficultyStats.easyTotal}
            color="text-green-600 dark:text-green-400"
          />
          <DifficultyCard
            label="Medium"
            solved={stats.difficultyStats.medium}
            total={stats.difficultyStats.mediumTotal}
            color="text-yellow-600 dark:text-yellow-400"
          />
          <DifficultyCard
            label="Hard"
            solved={stats.difficultyStats.hard}
            total={stats.difficultyStats.hardTotal}
            color="text-red-600 dark:text-red-400"
          />
        </div>
      </div>

      {/* ================================================================
       * Section 4: Activity Summary
       * Grid of secondary metrics: total attempts, hints used, total time,
       * and longest streak. Displayed in a single Card for visual grouping.
       * ================================================================ */}
      <div>
        <h3 className="text-lg font-semibold mb-4">Activity Summary</h3>
        <Card className="p-4">
          <div className="grid grid-cols-2 gap-4 text-sm">
            <div>
              <span className="text-muted-foreground">Total Attempts</span>
              <div className="font-semibold text-lg">{stats.totalAttempts}</div>
            </div>
            <div>
              <span className="text-muted-foreground">Hints Used</span>
              <div className="font-semibold text-lg">{stats.totalHints}</div>
            </div>
            <div>
              <span className="text-muted-foreground">Total Time</span>
              <div className="font-semibold text-lg">{formatDuration(stats.totalTimeMs)}</div>
            </div>
            <div>
              <span className="text-muted-foreground">Longest Streak</span>
              <div className="font-semibold text-lg">{stats.longestStreak} day{stats.longestStreak !== 1 ? 's' : ''}</div>
            </div>
          </div>
        </Card>
      </div>

      {/* ================================================================
       * Section 5: Due for Review
       * Lists problems scheduled for SRS review based on the SM-2 algorithm.
       * The ReviewSection handles hydration and empty states internally.
       * ================================================================ */}
      <div>
        <h3 className="text-lg font-semibold mb-4">Due for Review</h3>
        <ReviewSection problems={problems} />
      </div>

      {/* ================================================================
       * Section 6: Achievements
       * Grid of all achievements with visual distinction between locked
       * and unlocked states. The AchievementGrid is self-contained.
       * ================================================================ */}
      <div>
        <h3 className="text-lg font-semibold mb-4">Achievements</h3>
        <AchievementGrid />
      </div>
    </div>
  );
}

/* ========================================================================
 * StatCard -- Reusable summary metric card
 * ======================================================================== */

/**
 * A compact card displaying a single key metric with an icon, label, value,
 * and optional subtitle.
 *
 * @param props.icon - React node for the metric's icon (typically a lucide icon).
 * @param props.label - Short label describing the metric (e.g., "Solved").
 * @param props.value - The primary display value (e.g., "5/20").
 * @param props.subtitle - Optional secondary text below the value (e.g., "Best: 7").
 * @returns A metric card UI.
 */
function StatCard({
  icon,
  label,
  value,
  subtitle,
}: {
  icon: React.ReactNode;
  label: string;
  value: string;
  subtitle?: string;
}) {
  return (
    <Card className="p-4">
      <div className="flex items-center gap-2 mb-2">
        {icon}
        <span className="text-sm text-muted-foreground">{label}</span>
      </div>
      <div className="text-2xl font-bold">{value}</div>
      {subtitle && <div className="text-xs text-muted-foreground mt-1">{subtitle}</div>}
    </Card>
  );
}

/* ========================================================================
 * DifficultyCard -- Card for a single difficulty level
 * ======================================================================== */

/**
 * A centered card showing solved/total for a specific difficulty level.
 *
 * @param props.label - Difficulty name (e.g., "Easy", "Medium", "Hard").
 * @param props.solved - Number of problems solved at this difficulty.
 * @param props.total - Total number of problems at this difficulty.
 * @param props.color - Tailwind color classes for the difficulty badge text.
 * @returns A difficulty breakdown card UI.
 */
function DifficultyCard({
  label,
  solved,
  total,
  color,
}: {
  label: string;
  solved: number;
  total: number;
  color: string;
}) {
  return (
    <Card className="p-4 text-center">
      <Badge variant="outline" className={`mb-2 ${color}`}>
        {label}
      </Badge>
      <div className="text-xl font-bold">
        {solved}/{total}
      </div>
    </Card>
  );
}
