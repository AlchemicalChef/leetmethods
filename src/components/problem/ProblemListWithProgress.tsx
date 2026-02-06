'use client';

import { ProblemList } from './ProblemList';
import { useProgressStore } from '@/store/progressStore';
import type { ProblemSummary } from '@/lib/problems/types';

interface ProblemListWithProgressProps {
  problems: ProblemSummary[];
}

export function ProblemListWithProgress({ problems }: ProblemListWithProgressProps) {
  const { getCompletedSlugs } = useProgressStore();
  return <ProblemList problems={problems} completedSlugs={getCompletedSlugs()} />;
}
