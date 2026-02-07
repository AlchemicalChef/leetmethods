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
import { PrerequisitesBadge } from './PrerequisitesBadge';

interface ProblemListProps {
  problems: ProblemSummary[];
  completedSlugs: string[];
  prereqCounts?: Record<string, number>;
  dueSlugs?: Set<string>;
}

const difficultyColors: Record<Difficulty, string> = {
  easy: 'bg-green-100 text-green-800 dark:bg-green-900 dark:text-green-200',
  medium: 'bg-yellow-100 text-yellow-800 dark:bg-yellow-900 dark:text-yellow-200',
  hard: 'bg-red-100 text-red-800 dark:bg-red-900 dark:text-red-200',
};

const difficultyOrder: Record<Difficulty, number> = {
  easy: 1,
  medium: 2,
  hard: 3,
};

export function ProblemList({ problems, completedSlugs, prereqCounts = {}, dueSlugs = new Set() }: ProblemListProps) {
  const [search, setSearch] = useState('');
  const [difficultyFilter, setDifficultyFilter] = useState<Difficulty | 'all'>('all');
  const [categoryFilter, setCategoryFilter] = useState<Category | 'all'>('all');
  const [statusFilter, setStatusFilter] = useState<'all' | 'solved' | 'unsolved'>('all');

  const categories = useMemo(() => {
    const cats = new Set(problems.map((p) => p.category));
    return Array.from(cats).sort();
  }, [problems]);

  const filteredProblems = useMemo(() => {
    return problems
      .filter((problem) => {
        // Search filter
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

        // Status filter
        const isCompleted = completedSlugs.includes(problem.slug);
        if (statusFilter === 'solved' && !isCompleted) return false;
        if (statusFilter === 'unsolved' && isCompleted) return false;

        return true;
      })
      .sort((a, b) => {
        // Sort by difficulty, then by title
        const diffDiff = difficultyOrder[a.difficulty] - difficultyOrder[b.difficulty];
        if (diffDiff !== 0) return diffDiff;
        return a.title.localeCompare(b.title);
      });
  }, [problems, search, difficultyFilter, categoryFilter, statusFilter, completedSlugs]);

  return (
    <div className="space-y-4">
      {/* Filters */}
      <div className="flex flex-wrap gap-3">
        {/* Search */}
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

        {/* Difficulty filter */}
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

        {/* Category filter */}
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

        {/* Status filter */}
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

      {/* Stats */}
      <div className="text-sm text-muted-foreground">
        Showing {filteredProblems.length} of {problems.length} problems
        {completedSlugs.length > 0 && (
          <span className="ml-2">
            ({completedSlugs.length} solved)
          </span>
        )}
      </div>

      {/* Problem list */}
      <div className="space-y-2">
        {filteredProblems.map((problem) => {
          const isCompleted = completedSlugs.includes(problem.slug);
          const isDue = dueSlugs.has(problem.slug);
          const href = problem.isCustom
            ? `/problems/custom/${problem.slug}`
            : `/problems/${problem.slug}`;

          return (
            <Link key={problem.id} href={href}>
              <Card className="p-4 hover:bg-muted/50 transition-colors cursor-pointer">
                <div className="flex items-center gap-4">
                  {/* Status icon */}
                  <div className="flex-shrink-0">
                    {isDue ? (
                      <RefreshCw className="h-5 w-5 text-amber-500" />
                    ) : isCompleted ? (
                      <CheckCircle2 className="h-5 w-5 text-green-500" />
                    ) : (
                      <Circle className="h-5 w-5 text-muted-foreground" />
                    )}
                  </div>

                  {/* Title and tags */}
                  <div className="flex-1 min-w-0">
                    <div className="font-medium truncate">{problem.title}</div>
                    <div className="flex flex-wrap gap-1 mt-1">
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

                  {/* Badges */}
                  <div className="flex items-center gap-2 flex-shrink-0">
                    {problem.isCustom && (
                      <Badge variant="outline" className="bg-purple-50 text-purple-700 border-purple-200 dark:bg-purple-950/30 dark:text-purple-400 dark:border-purple-800">
                        Custom
                      </Badge>
                    )}
                    {(prereqCounts[problem.slug] ?? 0) > 0 && (
                      <PrerequisitesBadge unsatisfiedCount={prereqCounts[problem.slug]} />
                    )}
                    <Badge variant="outline" className="hidden sm:inline-flex">
                      {problem.category}
                    </Badge>
                    <Badge className={difficultyColors[problem.difficulty]}>
                      {problem.difficulty.charAt(0).toUpperCase() + problem.difficulty.slice(1)}
                    </Badge>
                  </div>
                </div>
              </Card>
            </Link>
          );
        })}

        {filteredProblems.length === 0 && (
          <div className="text-center py-12 text-muted-foreground">
            No problems found matching your filters.
          </div>
        )}
      </div>
    </div>
  );
}
