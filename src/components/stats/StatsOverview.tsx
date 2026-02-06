'use client';

import { useMemo } from 'react';
import { Card } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import { Trophy, Target, Flame, Clock } from 'lucide-react';
import { useProgressStore } from '@/store/progressStore';
import { computeStats, formatDuration } from '@/lib/stats';
import type { ProblemSummary, Category } from '@/lib/problems/types';
import { AchievementGrid } from '@/components/achievements/AchievementGrid';

interface StatsOverviewProps {
  problems: ProblemSummary[];
}

const categoryLabels: Record<Category, string> = {
  logic: 'Logic',
  induction: 'Induction',
  lists: 'Lists',
  arithmetic: 'Arithmetic',
  'data-structures': 'Data Structures',
  relations: 'Relations',
};

const categoryColors: Record<Category, string> = {
  logic: 'bg-blue-500',
  induction: 'bg-purple-500',
  lists: 'bg-emerald-500',
  arithmetic: 'bg-orange-500',
  'data-structures': 'bg-pink-500',
  relations: 'bg-cyan-500',
};

export function StatsOverview({ problems }: StatsOverviewProps) {
  const { progress, streakData } = useProgressStore();
  const stats = useMemo(
    () => computeStats(progress, problems, streakData),
    [progress, problems, streakData]
  );

  return (
    <div className="space-y-8">
      {/* Stat cards */}
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

      {/* Category progress */}
      <div>
        <h3 className="text-lg font-semibold mb-4">Progress by Category</h3>
        <div className="space-y-3">
          {stats.categoryStats.map((cat) => (
            <div key={cat.category}>
              <div className="flex items-center justify-between mb-1">
                <span className="text-sm font-medium">{categoryLabels[cat.category]}</span>
                <span className="text-sm text-muted-foreground">
                  {cat.solved}/{cat.total}
                </span>
              </div>
              <div className="h-2 bg-muted rounded-full overflow-hidden">
                <div
                  className={`h-full rounded-full transition-all duration-500 ${categoryColors[cat.category]}`}
                  style={{ width: `${cat.percent}%` }}
                />
              </div>
            </div>
          ))}
        </div>
      </div>

      {/* Difficulty breakdown */}
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

      {/* Activity summary */}
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
      {/* Achievements */}
      <div>
        <h3 className="text-lg font-semibold mb-4">Achievements</h3>
        <AchievementGrid />
      </div>
    </div>
  );
}

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
