'use client';

import Link from 'next/link';
import { Badge } from '@/components/ui/badge';
import { Card } from '@/components/ui/card';
import { ArrowRight } from 'lucide-react';
import type { ProblemSummary, Difficulty } from '@/lib/problems/types';

interface NextProblemCardProps {
  problem: ProblemSummary;
}

const difficultyColors: Record<Difficulty, string> = {
  easy: 'bg-green-100 text-green-800 dark:bg-green-900 dark:text-green-200',
  medium: 'bg-yellow-100 text-yellow-800 dark:bg-yellow-900 dark:text-yellow-200',
  hard: 'bg-red-100 text-red-800 dark:bg-red-900 dark:text-red-200',
};

export function NextProblemCard({ problem }: NextProblemCardProps) {
  return (
    <Link href={`/problems/${problem.slug}`}>
      <Card className="p-3 hover:bg-muted/50 transition-colors inline-flex items-center gap-3">
        <div className="flex items-center gap-2">
          <span className="text-sm font-medium">Next:</span>
          <span className="text-sm">{problem.title}</span>
          <Badge className={`text-xs ${difficultyColors[problem.difficulty]}`}>
            {problem.difficulty}
          </Badge>
        </div>
        <ArrowRight className="h-4 w-4 text-muted-foreground" />
      </Card>
    </Link>
  );
}
