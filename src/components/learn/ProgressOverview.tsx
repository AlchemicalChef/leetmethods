/**
 * @module ProgressOverview
 *
 * Displays an aggregate progress summary for all problems across all categories.
 *
 * This component appears at the top of the Learn page and gives users a
 * quick visual overview of:
 *   - Total problems solved out of total available (with percentage)
 *   - A full-width progress bar
 *   - Per-category breakdown showing solved/total for each category
 *
 * The component derives all data by cross-referencing the `progressStore`
 * (which tracks which problems the user has completed) against the full
 * list of available problems passed in as props.
 *
 * Design decisions:
 *   - The `problemSlugs` Set is used to ensure we only count completions for
 *     problems that actually exist in the current problem set, filtering out
 *     stale progress entries for problems that may have been removed.
 *   - Categories are dynamically derived from the problems array rather than
 *     hardcoded, so new categories are automatically included.
 *   - The `categoryLabels` map provides human-readable names for category slugs.
 *     If a category is not in the map, the raw slug is used as a fallback.
 */
'use client';

import { useProgressStore } from '@/store/progressStore';
import type { ProblemSummary, Category } from '@/lib/problems/types';

/**
 * Props for the ProgressOverview component.
 *
 * @property problems - Complete list of all problem summaries. Used to compute
 *   total counts and per-category breakdowns.
 */
interface ProgressOverviewProps {
  problems: ProblemSummary[];
}

/**
 * Maps category slug identifiers to user-facing display labels.
 * Falls back to the raw category string if a category is not found in this map.
 */
const categoryLabels: Record<Category, string> = {
  logic: 'Logic',
  booleans: 'Booleans',
  induction: 'Induction',
  lists: 'Lists',
  arithmetic: 'Arithmetic',
  'data-structures': 'Data Structures',
  relations: 'Relations',
};

/**
 * Renders an aggregate progress overview with an overall progress bar and
 * per-category completion counts.
 *
 * @param props - Component props containing all available problem summaries.
 * @returns A progress card with overall and per-category statistics.
 */
export function ProgressOverview({ problems }: ProgressOverviewProps) {
  /* Subscribe to the progress record from the persisted Zustand store */
  const progress = useProgressStore((s) => s.progress);

  /* Build a Set of valid problem slugs to filter out stale progress entries
     for problems that no longer exist in the current problem set */
  const problemSlugs = new Set(problems.map((p) => p.slug));

  /* Count only completions for problems that exist in the current problem set.
     This prevents inflated counts if problems are ever removed. */
  const completedCount = Object.entries(progress).filter(
    ([slug, p]) => p.completed && problemSlugs.has(slug)
  ).length;
  const totalCount = problems.length;

  /* Calculate percentage, guarding against division by zero */
  const percent = totalCount > 0 ? Math.round((completedCount / totalCount) * 100) : 0;

  /* Extract unique categories from the problems array to dynamically build
     the per-category breakdown grid */
  const categories = Array.from(new Set(problems.map((p) => p.category)));

  return (
    <div className="bg-muted/30 rounded-lg p-4">
      {/* Header row: label on the left, numeric summary on the right */}
      <div className="flex items-center justify-between mb-3">
        <span className="font-medium">Your Progress</span>
        <span className="text-sm text-muted-foreground">
          {completedCount}/{totalCount} solved ({percent}%)
        </span>
      </div>

      {/* Full-width progress bar with smooth animation on percentage changes */}
      <div className="h-2 bg-muted rounded-full overflow-hidden mb-4">
        <div
          className="h-full bg-primary rounded-full transition-all duration-500"
          style={{ width: `${percent}%` }}
        />
      </div>

      {/* Per-category breakdown grid.
          Uses a responsive grid: 2 columns on small screens, 3 on medium+.
          Each cell shows the category label and its solved/total count. */}
      <div className="grid grid-cols-2 md:grid-cols-3 gap-2 text-sm">
        {categories.map((cat) => {
          /* Filter problems belonging to this category */
          const catProblems = problems.filter((p) => p.category === cat);
          /* Count how many of those are completed */
          const catCompleted = catProblems.filter((p) => progress[p.slug]?.completed).length;
          return (
            <div key={cat} className="flex items-center justify-between px-2 py-1 bg-background rounded">
              {/* Use the human-readable label, falling back to the raw category slug */}
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
