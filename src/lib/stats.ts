/**
 * Statistics computation module for the LeetMethods stats dashboard.
 *
 * Aggregates raw progress data (per-problem completion, timing, attempts, hints)
 * and problem metadata into structured statistics for display on the `/stats` page.
 *
 * Key design decisions:
 * - Only counts completions for known (built-in) problems, excluding custom or
 *   orphaned progress entries that may linger in localStorage after problem removal.
 * - Category stats are ordered using the canonical `CATEGORY_ORDER` from ui-constants,
 *   ensuring consistent display order across the application.
 * - Average solve time only considers problems that have a positive recorded duration,
 *   avoiding division artifacts from problems where timing was not tracked.
 *
 * This module is a pure function library with no side effects or state.
 *
 * @module stats
 */

import type { ProblemProgress, StreakData } from '@/lib/types/progress';
import type { ProblemSummary, Category } from '@/lib/problems/types';
import { CATEGORY_ORDER } from '@/lib/ui-constants';

/* ============================================================================
 * Type Definitions
 * ========================================================================= */

/**
 * Complete statistics snapshot for the stats dashboard.
 *
 * @property totalProblems - Total number of built-in problems available.
 * @property solvedCount - Number of problems the user has completed.
 * @property completionPercent - Rounded percentage of problems completed (0-100).
 * @property currentStreak - Number of consecutive days the user has solved at least one problem.
 * @property longestStreak - All-time longest streak in days.
 * @property totalTimeMs - Cumulative solve time across all completed problems in milliseconds.
 * @property averageTimeMs - Average solve time per timed problem in milliseconds.
 * @property categoryStats - Per-category breakdown of solved vs. total problems.
 * @property difficultyStats - Per-difficulty breakdown of solved vs. total problems.
 * @property totalAttempts - Sum of all attempts across all problems (including incomplete ones).
 * @property totalHints - Sum of all hints used across all problems.
 */
export interface StatsData {
  totalProblems: number;
  solvedCount: number;
  completionPercent: number;
  currentStreak: number;
  longestStreak: number;
  totalTimeMs: number;
  averageTimeMs: number;
  categoryStats: CategoryStat[];
  difficultyStats: { easy: number; medium: number; hard: number; easyTotal: number; mediumTotal: number; hardTotal: number };
  totalAttempts: number;
  totalHints: number;
}

/**
 * Statistics for a single problem category.
 *
 * @property category - The category identifier (e.g., 'logic', 'induction').
 * @property solved - Number of completed problems in this category.
 * @property total - Total number of problems in this category.
 * @property percent - Rounded completion percentage for this category (0-100).
 */
export interface CategoryStat {
  category: Category;
  solved: number;
  total: number;
  percent: number;
}

/* ============================================================================
 * Statistics Computation
 * ========================================================================= */

/**
 * Computes a complete statistics snapshot from the user's progress, the problem list,
 * and streak data.
 *
 * @param progress - The full progress record keyed by problem slug.
 * @param problems - All known (built-in) problem summaries. Custom problems are excluded
 *                   by the caller.
 * @param streakData - The user's current and historical streak information.
 * @returns A `StatsData` object containing all computed statistics.
 */
export function computeStats(
  progress: Record<string, ProblemProgress>,
  problems: ProblemSummary[],
  streakData: StreakData
): StatsData {
  const totalProblems = problems.length;

  /**
   * Build a set of known slugs to filter progress entries. This prevents
   * orphaned progress (from deleted problems) or custom problem progress
   * from being counted in the official statistics.
   */
  const problemSlugs = new Set(problems.map((p) => p.slug));
  const completedProblems = Object.entries(progress)
    .filter(([slug, p]) => p.completed && problemSlugs.has(slug))
    .map(([, p]) => p);
  const solvedCount = completedProblems.length;
  const completionPercent = totalProblems > 0 ? Math.round((solvedCount / totalProblems) * 100) : 0;

  /**
   * Timing statistics: sum all recorded durations, but only average over
   * problems that actually have a positive duration recorded. Problems
   * solved before timing was implemented will have null/zero durations.
   */
  const totalTimeMs = completedProblems.reduce((sum, p) => sum + (p.solveDurationMs ?? 0), 0);
  const timedSolves = completedProblems.filter((p) => p.solveDurationMs && p.solveDurationMs > 0);
  const averageTimeMs = timedSolves.length > 0 ? totalTimeMs / timedSolves.length : 0;

  /* -- Category statistics: ordered by the canonical CATEGORY_ORDER -- */
  const categoryMap = new Map<Category, { solved: number; total: number }>();
  for (const cat of CATEGORY_ORDER) {
    categoryMap.set(cat, { solved: 0, total: 0 });
  }
  for (const prob of problems) {
    const entry = categoryMap.get(prob.category) ?? { solved: 0, total: 0 };
    entry.total++;
    if (progress[prob.slug]?.completed) {
      entry.solved++;
    }
    categoryMap.set(prob.category, entry);
  }
  const categoryStats: CategoryStat[] = CATEGORY_ORDER
    .filter((cat) => categoryMap.has(cat) && (categoryMap.get(cat)!.total > 0))
    .map((cat) => {
      const data = categoryMap.get(cat)!;
      return {
        category: cat,
        solved: data.solved,
        total: data.total,
        percent: data.total > 0 ? Math.round((data.solved / data.total) * 100) : 0,
      };
    });

  /* -- Difficulty statistics: count solved and total for each difficulty level -- */
  const difficultyStats = { easy: 0, medium: 0, hard: 0, easyTotal: 0, mediumTotal: 0, hardTotal: 0 };
  for (const prob of problems) {
    difficultyStats[`${prob.difficulty}Total` as keyof typeof difficultyStats]++;
    if (progress[prob.slug]?.completed) {
      difficultyStats[prob.difficulty as 'easy' | 'medium' | 'hard']++;
    }
  }

  /**
   * Aggregate attempt and hint counts across ALL progress entries (not just
   * completed ones). This gives an accurate picture of total effort, including
   * problems the user is still working on.
   */
  const totalAttempts = Object.values(progress).reduce((sum, p) => sum + p.attempts, 0);
  const totalHints = Object.values(progress).reduce((sum, p) => sum + p.hintsUsed, 0);

  return {
    totalProblems,
    solvedCount,
    completionPercent,
    currentStreak: streakData.currentStreak,
    longestStreak: streakData.longestStreak,
    totalTimeMs,
    averageTimeMs,
    categoryStats,
    difficultyStats,
    totalAttempts,
    totalHints,
  };
}

/* ============================================================================
 * Formatting Utilities
 * ========================================================================= */

/**
 * Formats a duration in milliseconds into a human-readable string.
 *
 * The output adapts to the magnitude of the duration:
 * - Under 60 seconds: "42s"
 * - Under 60 minutes: "3m 25s"
 * - 60 minutes or more: "1h 23m"
 *
 * Returns '--' for zero durations, which indicates that no timing data
 * was recorded for the problem.
 *
 * @param ms - Duration in milliseconds.
 * @returns A human-readable duration string, or '--' if `ms` is zero.
 */
export function formatDuration(ms: number): string {
  if (ms === 0) return '--';
  const seconds = Math.floor(ms / 1000);
  if (seconds < 60) return `${seconds}s`;
  const minutes = Math.floor(seconds / 60);
  const remainingSeconds = seconds % 60;
  if (minutes < 60) return `${minutes}m ${remainingSeconds}s`;
  const hours = Math.floor(minutes / 60);
  const remainingMinutes = minutes % 60;
  return `${hours}h ${remainingMinutes}m`;
}
