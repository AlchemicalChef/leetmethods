/**
 * @module ProblemListWithProgress
 *
 * A wrapper around ProblemList that connects it to the Zustand stores for
 * progress tracking, custom problems, and SRS review scheduling.
 *
 * This component exists to separate the presentational ProblemList from
 * the store-dependent logic. ProblemList is a pure component that receives
 * all data as props, while this wrapper:
 *
 * 1. Reads completed problem slugs from `progressStore`
 * 2. Merges built-in problems with user-created custom problems from
 *    `customProblemStore`
 * 3. Computes prerequisite satisfaction counts for each problem
 * 4. Computes which problems are due for SRS review
 *
 * This separation makes ProblemList easier to test and reuse, while keeping
 * the Zustand coupling in a single thin wrapper.
 *
 * Design decisions:
 * - All derived data (completedSlugs, allProblems, prereqCounts, dueSlugs) is
 *   memoized to avoid expensive recomputation on every render.
 * - The getDueReviews call is wrapped in try/catch because it can throw if
 *   the progress store has corrupt data (e.g., from a schema migration issue).
 * - Custom problem summaries are appended after built-in problems so they
 *   appear at the end of the list (ProblemList sorts by difficulty/title anyway).
 *
 * @see {@link ProblemList} for the presentational list component
 * @see {@link progressStore} for completion and SRS data
 * @see {@link customProblemStore} for user-created problems
 */
'use client';

import { useMemo } from 'react';
import { ProblemList } from './ProblemList';
import { useProgressStore } from '@/store/progressStore';
import { useCustomProblemStore } from '@/store/customProblemStore';
import { getPrerequisiteStatus, getUnsatisfiedCount } from '@/lib/prerequisites';
import type { Problem, ProblemSummary } from '@/lib/problems/types';

/* ============================================================================
 * Types
 * ============================================================================ */

/**
 * Props for the ProblemListWithProgress wrapper.
 */
interface ProblemListWithProgressProps {
  /** Built-in problem summaries (loaded at build time from JSON content files) */
  problems: ProblemSummary[];
  /** Full problem objects needed for prerequisite computation (optional) */
  fullProblems?: Problem[];
}

/* ============================================================================
 * ProblemListWithProgress Component
 * ============================================================================ */

/**
 * Store-connected wrapper that provides progress data to ProblemList.
 *
 * @param props - See {@link ProblemListWithProgressProps}
 * @returns ProblemList with store-derived progress data
 */
export function ProblemListWithProgress({ problems, fullProblems = [] }: ProblemListWithProgressProps) {
  /** Raw progress map from the persisted Zustand store */
  const progress = useProgressStore((s) => s.progress);

  /** Extract slugs of all completed problems */
  const completedSlugs = useMemo(
    () => Object.values(progress).filter((p) => p.completed).map((p) => p.slug),
    [progress]
  );

  /** Get custom problem summaries from the custom problem store */
  const getCustomSummaries = useCustomProblemStore((s) => s.getCustomSummaries);

  /** Function to get problems due for SRS review */
  const getDueReviews = useProgressStore((s) => s.getDueReviews);

  /**
   * Merge built-in problems with user-created custom problems.
   * Custom problems are appended so they sort naturally with the rest.
   */
  const allProblems = useMemo(() => {
    const custom = getCustomSummaries();
    return [...problems, ...custom];
  }, [problems, getCustomSummaries]);

  /**
   * Compute the number of unsatisfied prerequisites for each problem.
   * Only computed when full problem objects are available (they contain
   * the prerequisites field that summaries lack).
   * Returns a sparse map -- only problems with unsatisfied prereqs have entries.
   */
  const prereqCounts = useMemo(() => {
    if (fullProblems.length === 0) return {};
    const counts: Record<string, number> = {};
    for (const p of fullProblems) {
      if (p.prerequisites) {
        const status = getPrerequisiteStatus(p, completedSlugs, fullProblems);
        const count = getUnsatisfiedCount(status);
        if (count > 0) counts[p.slug] = count;
      }
    }
    return counts;
  }, [fullProblems, completedSlugs]);

  /**
   * Compute the set of problem slugs due for SRS review.
   * Wrapped in try/catch to handle potential errors from corrupt progress data
   * or schema migration edge cases.
   */
  const dueSlugs = useMemo(() => {
    if (!getDueReviews) return new Set<string>();
    try {
      const reviews = getDueReviews();
      return new Set(reviews.map((r) => r.slug));
    } catch {
      return new Set<string>();
    }
  }, [getDueReviews]);

  return (
    <ProblemList
      problems={allProblems}
      completedSlugs={completedSlugs}
      prereqCounts={prereqCounts}
      dueSlugs={dueSlugs}
    />
  );
}
