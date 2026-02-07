'use client';

import { useMemo } from 'react';
import { ProblemList } from './ProblemList';
import { useProgressStore } from '@/store/progressStore';
import { useCustomProblemStore } from '@/store/customProblemStore';
import { getPrerequisiteStatus, getUnsatisfiedCount } from '@/lib/prerequisites';
import type { Problem, ProblemSummary } from '@/lib/problems/types';

interface ProblemListWithProgressProps {
  problems: ProblemSummary[];
  fullProblems?: Problem[];
}

export function ProblemListWithProgress({ problems, fullProblems = [] }: ProblemListWithProgressProps) {
  const progress = useProgressStore((s) => s.progress);
  const completedSlugs = useMemo(
    () => Object.values(progress).filter((p) => p.completed).map((p) => p.slug),
    [progress]
  );
  const getCustomSummaries = useCustomProblemStore((s) => s.getCustomSummaries);
  const getDueReviews = useProgressStore((s) => s.getDueReviews);

  const allProblems = useMemo(() => {
    const custom = getCustomSummaries();
    return [...problems, ...custom];
  }, [problems, getCustomSummaries]);

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
