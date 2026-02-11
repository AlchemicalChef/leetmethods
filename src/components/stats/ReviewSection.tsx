/**
 * @module ReviewSection
 *
 * Displays a list of problems that are due for spaced repetition review.
 *
 * This component integrates with the SM-2 spaced repetition system built
 * into the `progressStore`. Problems become "due" when their `nextReviewAt`
 * timestamp is in the past. Each due problem is shown as a card with the
 * problem title, category, how overdue it is, and a "Review" button that
 * links to the problem page with a `?review=true` query parameter.
 *
 * Design decisions:
 *   - **Hydration guard**: The component uses a `hydrated` flag that flips
 *     to `true` after the first mount. Before hydration, `getDueReviews()`
 *     would return stale/empty data because Zustand's localStorage
 *     rehydration hasn't completed yet. The guard ensures we only call
 *     `getDueReviews()` after the client has fully hydrated.
 *   - **Progress subscription (M5 fix)**: The component explicitly subscribes
 *     to `s.progress` even though it doesn't directly use the value. This
 *     ensures the component re-renders when progress changes (e.g., after
 *     completing a review), since `getDueReviews` is a derived function
 *     that reads from progress internally. Without this subscription, the
 *     component would not update after a review is submitted.
 *   - **Problem lookup map**: A `Map<slug, ProblemSummary>` is built from
 *     the problems array for O(1) slug-to-problem lookups when rendering
 *     review cards. Problems not found in the map are silently skipped
 *     (they may have been removed from the problem set).
 */
'use client';

import { useState, useEffect } from 'react';
import Link from 'next/link';
import { Card } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import { Button } from '@/components/ui/button';
import { RefreshCw } from 'lucide-react';
import { useProgressStore } from '@/store/progressStore';
import type { ProblemSummary } from '@/lib/problems/types';

/**
 * Props for the ReviewSection component.
 *
 * @property problems - Full list of problem summaries, used to look up
 *   display metadata (title, category) for due review slugs.
 */
interface ReviewSectionProps {
  problems: ProblemSummary[];
}

/**
 * Renders a list of problems due for SRS review, or an empty state message
 * if no reviews are currently due.
 *
 * @param props - Component props containing all available problem summaries.
 * @returns A list of review cards or an empty state placeholder.
 */
export function ReviewSection({ problems }: ReviewSectionProps) {
  /**
   * Hydration guard flag. Starts false (SSR/initial render) and flips to
   * true after the first client-side mount. This prevents calling
   * `getDueReviews()` before Zustand has rehydrated from localStorage.
   */
  const [hydrated, setHydrated] = useState(false);
  useEffect(() => { setHydrated(true); }, []);

  /** Selector for the getDueReviews function from the progress store */
  const getDueReviews = useProgressStore((s) => s.getDueReviews);

  /**
   * Subscribe to the raw progress object to trigger re-renders when
   * review data changes. Without this, the component would miss updates
   * because `getDueReviews` is a stable function reference (M5 fix).
   */
  useProgressStore((s) => s.progress);

  /** Only compute due reviews after hydration to avoid stale/empty results */
  const dueReviews = hydrated ? getDueReviews() : [];

  /** O(1) lookup map from problem slug to problem summary for rendering */
  const problemMap = new Map(problems.map((p) => [p.slug, p]));

  /* Empty state -- shown when there are no reviews due */
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
        /* Look up the problem metadata for this review slug.
           Skip rendering if the problem no longer exists in the problem set. */
        const problem = problemMap.get(review.slug);
        if (!problem) return null;

        return (
          <Card key={review.slug} className="p-3 flex items-center justify-between">
            {/* Problem info: title, category badge, and overdue indicator */}
            <div className="flex-1 min-w-0">
              <div className="font-medium text-sm truncate">{problem.title}</div>
              <div className="flex items-center gap-2 mt-0.5">
                <Badge variant="outline" className="text-xs">
                  {problem.category}
                </Badge>
                {/* Overdue indicator: shows "Due today" or "Nd overdue" in amber */}
                <span className="text-xs text-amber-600 dark:text-amber-400">
                  {review.overdueDays === 0 ? 'Due today' : `${review.overdueDays}d overdue`}
                </span>
              </div>
            </div>

            {/* Review button -- links to the problem page with review=true param.
                The query parameter signals the ProblemSolver to show review-specific
                UI or behavior (e.g., SRS quality rating after completion). */}
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
