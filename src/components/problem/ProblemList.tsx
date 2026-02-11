/**
 * @module ProblemList
 *
 * A filterable, sortable list of Coq proof problems with search, difficulty,
 * category, and completion status filters.
 *
 * This component is the primary problem browsing UI on the /problems page.
 * It renders each problem as a clickable card showing the title, tags,
 * difficulty, category, completion status, and SRS review due status.
 *
 * Features:
 * - **Text search**: Filters by title, tags, and category (case-insensitive)
 * - **Difficulty filter**: Easy / Medium / Hard
 * - **Category filter**: Dynamically populated from the problem set
 * - **Status filter**: All / Solved / Unsolved
 * - **Sorting**: Primary by difficulty (easy -> medium -> hard), secondary by title
 * - **Status icons**: Checkmark for completed, refresh for SRS review due, circle for unsolved
 * - **Prerequisites badge**: Shows count of unsatisfied prerequisites
 *
 * Design decisions:
 * - Filters are client-side since all problems are loaded at build time
 *   (no backend/pagination needed for the ~50-100 problem scale).
 * - Categories are dynamically extracted from the problem set rather than
 *   hardcoded, so adding a new category only requires adding problems.
 * - Tags are truncated to 3 per problem card to prevent layout overflow.
 * - The component is stateless with respect to progress -- it receives
 *   `completedSlugs` and `dueSlugs` as props from the parent wrapper
 *   (ProblemListWithProgress) which handles the Zustand store connection.
 *
 * @see {@link ProblemListWithProgress} for the store-connected wrapper
 * @see {@link PrerequisitesBadge} for the prerequisite count indicator
 */
'use client';

import { useState, useMemo } from 'react';
import Link from 'next/link';
import { Badge } from '@/components/ui/badge';
import { Card } from '@/components/ui/card';
import {
  Select,
  SelectContent,
  SelectItem,
  SelectTrigger,
  SelectValue,
} from '@/components/ui/select';
import { CheckCircle2, Circle, Search, RefreshCw } from 'lucide-react';
import type { ProblemSummary, Difficulty, Category } from '@/lib/problems/types';
import { DIFFICULTY_COLORS, DIFFICULTY_ORDER } from '@/lib/ui-constants';
import { PrerequisitesBadge } from './PrerequisitesBadge';

/* ============================================================================
 * Types
 * ============================================================================ */

/**
 * Props for the ProblemList component.
 */
interface ProblemListProps {
  /** Array of all problem summaries to display */
  problems: ProblemSummary[];
  /** Slugs of problems the user has completed */
  completedSlugs: string[];
  /** Map of problem slug -> count of unsatisfied prerequisites */
  prereqCounts?: Record<string, number>;
  /** Set of problem slugs that are due for SRS review */
  dueSlugs?: Set<string>;
}

/* ============================================================================
 * ProblemList Component
 * ============================================================================ */

/**
 * Filterable and sortable list of Coq proof problems.
 *
 * @param props - See {@link ProblemListProps}
 * @returns The filter controls and problem card list
 */
export function ProblemList({ problems, completedSlugs, prereqCounts = {}, dueSlugs = new Set() }: ProblemListProps) {
  /* --- Filter state --- */
  const [search, setSearch] = useState('');
  const [difficultyFilter, setDifficultyFilter] = useState<Difficulty | 'all'>('all');
  const [categoryFilter, setCategoryFilter] = useState<Category | 'all'>('all');
  const [statusFilter, setStatusFilter] = useState<'all' | 'solved' | 'unsolved'>('all');

  /**
   * Dynamically extract unique categories from the problem set.
   * Sorted alphabetically for consistent dropdown ordering.
   */
  const categories = useMemo(() => {
    const cats = new Set(problems.map((p) => p.category));
    return Array.from(cats).sort();
  }, [problems]);

  /**
   * Apply all active filters and sort the results.
   *
   * Filtering order: search -> difficulty -> category -> status
   * Sorting: primary by difficulty order (DIFFICULTY_ORDER), secondary alphabetical by title
   */
  const filteredProblems = useMemo(() => {
    return problems
      .filter((problem) => {
        // Text search: match against title, tags, or category
        if (search) {
          const searchLower = search.toLowerCase();
          const matches =
            problem.title.toLowerCase().includes(searchLower) ||
            problem.tags.some((t) => t.toLowerCase().includes(searchLower)) ||
            problem.category.toLowerCase().includes(searchLower);
          if (!matches) return false;
        }

        // Difficulty filter
        if (difficultyFilter !== 'all' && problem.difficulty !== difficultyFilter) {
          return false;
        }

        // Category filter
        if (categoryFilter !== 'all' && problem.category !== categoryFilter) {
          return false;
        }

        // Completion status filter
        const isCompleted = completedSlugs.includes(problem.slug);
        if (statusFilter === 'solved' && !isCompleted) return false;
        if (statusFilter === 'unsolved' && isCompleted) return false;

        return true;
      })
      .sort((a, b) => {
        // Primary sort: difficulty (easy < medium < hard)
        const diffDiff = DIFFICULTY_ORDER[a.difficulty] - DIFFICULTY_ORDER[b.difficulty];
        if (diffDiff !== 0) return diffDiff;
        // Secondary sort: alphabetical by title
        return a.title.localeCompare(b.title);
      });
  }, [problems, search, difficultyFilter, categoryFilter, statusFilter, completedSlugs]);

  return (
    <div className="space-y-4">
      {/* Filter controls row */}
      <div className="flex flex-wrap gap-3">
        {/* Text search input with search icon */}
        <div className="relative flex-1 min-w-[200px]">
          <Search className="absolute left-3 top-1/2 -translate-y-1/2 h-4 w-4 text-muted-foreground" />
          <input
            type="text"
            placeholder="Search problems..."
            value={search}
            onChange={(e) => setSearch(e.target.value)}
            className="w-full pl-9 pr-3 py-2 border rounded-md bg-background"
          />
        </div>

        {/* Difficulty dropdown filter */}
        <Select value={difficultyFilter} onValueChange={(v) => setDifficultyFilter(v as Difficulty | 'all')}>
          <SelectTrigger className="w-[130px]">
            <SelectValue placeholder="Difficulty" />
          </SelectTrigger>
          <SelectContent>
            <SelectItem value="all">All Levels</SelectItem>
            <SelectItem value="easy">Easy</SelectItem>
            <SelectItem value="medium">Medium</SelectItem>
            <SelectItem value="hard">Hard</SelectItem>
          </SelectContent>
        </Select>

        {/* Category dropdown filter -- dynamically populated */}
        <Select value={categoryFilter} onValueChange={(v) => setCategoryFilter(v as Category | 'all')}>
          <SelectTrigger className="w-[150px]">
            <SelectValue placeholder="Category" />
          </SelectTrigger>
          <SelectContent>
            <SelectItem value="all">All Categories</SelectItem>
            {categories.map((cat) => (
              <SelectItem key={cat} value={cat}>
                {cat.charAt(0).toUpperCase() + cat.slice(1)}
              </SelectItem>
            ))}
          </SelectContent>
        </Select>

        {/* Completion status dropdown filter */}
        <Select value={statusFilter} onValueChange={(v) => setStatusFilter(v as 'all' | 'solved' | 'unsolved')}>
          <SelectTrigger className="w-[130px]">
            <SelectValue placeholder="Status" />
          </SelectTrigger>
          <SelectContent>
            <SelectItem value="all">All Status</SelectItem>
            <SelectItem value="solved">Solved</SelectItem>
            <SelectItem value="unsolved">Unsolved</SelectItem>
          </SelectContent>
        </Select>
      </div>

      {/* Results count and solved count summary */}
      <div className="text-sm text-muted-foreground">
        Showing {filteredProblems.length} of {problems.length} problems
        {completedSlugs.length > 0 && (
          <span className="ml-2">
            ({completedSlugs.length} solved)
          </span>
        )}
      </div>

      {/* Problem cards list */}
      <div className="space-y-2">
        {filteredProblems.map((problem) => {
          const isCompleted = completedSlugs.includes(problem.slug);
          const isDue = dueSlugs.has(problem.slug);
          // Custom problems use a different URL path segment
          const href = problem.isCustom
            ? `/problems/custom/${problem.slug}`
            : `/problems/${problem.slug}`;

          return (
            <Link key={problem.id} href={href}>
              <Card className="p-4 hover:bg-muted/50 transition-colors cursor-pointer">
                <div className="flex items-center gap-4">
                  {/* Status icon: review due (amber), completed (green), or unsolved (gray) */}
                  <div className="flex-shrink-0">
                    {isDue ? (
                      <RefreshCw className="h-5 w-5 text-amber-500" />
                    ) : isCompleted ? (
                      <CheckCircle2 className="h-5 w-5 text-green-500" />
                    ) : (
                      <Circle className="h-5 w-5 text-muted-foreground" />
                    )}
                  </div>

                  {/* Problem title and truncated tags */}
                  <div className="flex-1 min-w-0">
                    <div className="font-medium truncate">{problem.title}</div>
                    <div className="flex flex-wrap gap-1 mt-1">
                      {/* Show at most 3 tags to prevent layout overflow */}
                      {problem.tags.slice(0, 3).map((tag) => (
                        <span
                          key={tag}
                          className="text-xs text-muted-foreground bg-muted px-1.5 py-0.5 rounded"
                        >
                          {tag}
                        </span>
                      ))}
                    </div>
                  </div>

                  {/* Right-side badges: custom indicator, prereqs, category, difficulty */}
                  <div className="flex items-center gap-2 flex-shrink-0">
                    {problem.isCustom && (
                      <Badge variant="outline" className="bg-purple-50 text-purple-700 border-purple-200 dark:bg-purple-950/30 dark:text-purple-400 dark:border-purple-800">
                        Custom
                      </Badge>
                    )}
                    {(prereqCounts[problem.slug] ?? 0) > 0 && (
                      <PrerequisitesBadge unsatisfiedCount={prereqCounts[problem.slug]} />
                    )}
                    {/* Category badge hidden on small screens to save space */}
                    <Badge variant="outline" className="hidden sm:inline-flex">
                      {problem.category}
                    </Badge>
                    <Badge className={DIFFICULTY_COLORS[problem.difficulty]}>
                      {problem.difficulty.charAt(0).toUpperCase() + problem.difficulty.slice(1)}
                    </Badge>
                  </div>
                </div>
              </Card>
            </Link>
          );
        })}

        {/* Empty state when no problems match the active filters */}
        {filteredProblems.length === 0 && (
          <div className="text-center py-12 text-muted-foreground">
            No problems found matching your filters.
          </div>
        )}
      </div>
    </div>
  );
}
