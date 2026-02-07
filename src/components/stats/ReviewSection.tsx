'use client';

import Link from 'next/link';
import { Card } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import { Button } from '@/components/ui/button';
import { RefreshCw } from 'lucide-react';
import { useProgressStore } from '@/store/progressStore';
import type { ProblemSummary } from '@/lib/problems/types';

interface ReviewSectionProps {
  problems: ProblemSummary[];
}

export function ReviewSection({ problems }: ReviewSectionProps) {
  const getDueReviews = useProgressStore((s) => s.getDueReviews);
  const dueReviews = getDueReviews();
  const problemMap = new Map(problems.map((p) => [p.slug, p]));

  if (dueReviews.length === 0) {
    return (
      <Card className="p-6 text-center text-muted-foreground">
        <RefreshCw className="h-6 w-6 mx-auto mb-2 opacity-40" />
        <p className="text-sm">No reviews due right now</p>
        <p className="text-xs mt-1">Complete problems to start building your review schedule</p>
      </Card>
    );
  }

  return (
    <div className="space-y-2">
      {dueReviews.map((review) => {
        const problem = problemMap.get(review.slug);
        if (!problem) return null;

        return (
          <Card key={review.slug} className="p-3 flex items-center justify-between">
            <div className="flex-1 min-w-0">
              <div className="font-medium text-sm truncate">{problem.title}</div>
              <div className="flex items-center gap-2 mt-0.5">
                <Badge variant="outline" className="text-xs">
                  {problem.category}
                </Badge>
                <span className="text-xs text-amber-600 dark:text-amber-400">
                  {review.overdueDays === 0 ? 'Due today' : `${review.overdueDays}d overdue`}
                </span>
              </div>
            </div>
            <Button asChild size="sm" variant="outline">
              <Link href={`/problems/${problem.slug}?review=true`}>
                <RefreshCw className="h-3 w-3 mr-1" />
                Review
              </Link>
            </Button>
          </Card>
        );
      })}
    </div>
  );
}
