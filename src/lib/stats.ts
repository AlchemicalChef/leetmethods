import type { ProblemProgress, StreakData } from '@/lib/types/progress';
import type { ProblemSummary, Category } from '@/lib/problems/types';
import { CATEGORY_ORDER } from '@/lib/ui-constants';

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

export interface CategoryStat {
  category: Category;
  solved: number;
  total: number;
  percent: number;
}

export function computeStats(
  progress: Record<string, ProblemProgress>,
  problems: ProblemSummary[],
  streakData: StreakData
): StatsData {
  const totalProblems = problems.length;
  const completedProblems = Object.values(progress).filter((p) => p.completed);
  const solvedCount = completedProblems.length;
  const completionPercent = totalProblems > 0 ? Math.round((solvedCount / totalProblems) * 100) : 0;

  const totalTimeMs = completedProblems.reduce((sum, p) => sum + (p.solveDurationMs ?? 0), 0);
  const timedSolves = completedProblems.filter((p) => p.solveDurationMs && p.solveDurationMs > 0);
  const averageTimeMs = timedSolves.length > 0 ? totalTimeMs / timedSolves.length : 0;

  // Category stats
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

  // Difficulty stats
  const difficultyStats = { easy: 0, medium: 0, hard: 0, easyTotal: 0, mediumTotal: 0, hardTotal: 0 };
  for (const prob of problems) {
    difficultyStats[`${prob.difficulty}Total` as keyof typeof difficultyStats]++;
    if (progress[prob.slug]?.completed) {
      difficultyStats[prob.difficulty as 'easy' | 'medium' | 'hard']++;
    }
  }

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
