'use client';

import { useProgressStore } from '@/store/progressStore';
import type { ProblemSummary, Category } from '@/lib/problems/types';

interface ProgressOverviewProps {
  problems: ProblemSummary[];
}

const categoryLabels: Record<Category, string> = {
  logic: 'Logic',
  booleans: 'Booleans',
  induction: 'Induction',
  lists: 'Lists',
  arithmetic: 'Arithmetic',
  'data-structures': 'Data Structures',
  relations: 'Relations',
};

export function ProgressOverview({ problems }: ProgressOverviewProps) {
  const { progress } = useProgressStore();
  const completedCount = Object.values(progress).filter((p) => p.completed).length;
  const totalCount = problems.length;
  const percent = totalCount > 0 ? Math.round((completedCount / totalCount) * 100) : 0;

  const categories = Array.from(new Set(problems.map((p) => p.category)));

  return (
    <div className="bg-muted/30 rounded-lg p-4">
      <div className="flex items-center justify-between mb-3">
        <span className="font-medium">Your Progress</span>
        <span className="text-sm text-muted-foreground">
          {completedCount}/{totalCount} solved ({percent}%)
        </span>
      </div>
      <div className="h-2 bg-muted rounded-full overflow-hidden mb-4">
        <div
          className="h-full bg-primary rounded-full transition-all duration-500"
          style={{ width: `${percent}%` }}
        />
      </div>
      <div className="grid grid-cols-2 md:grid-cols-3 gap-2 text-sm">
        {categories.map((cat) => {
          const catProblems = problems.filter((p) => p.category === cat);
          const catCompleted = catProblems.filter((p) => progress[p.slug]?.completed).length;
          return (
            <div key={cat} className="flex items-center justify-between px-2 py-1 bg-background rounded">
              <span>{categoryLabels[cat] ?? cat}</span>
              <span className="text-muted-foreground">
                {catCompleted}/{catProblems.length}
              </span>
            </div>
          );
        })}
      </div>
    </div>
  );
}
