/**
 * @module NextProblemCard
 *
 * A compact inline card that links to the next recommended problem after
 * a successful proof submission.
 *
 * This component appears in two places:
 * 1. Inside the submission success banner in ProblemSolver (above the editor)
 * 2. Inside the GoalsPanel completion view (in the goals area)
 *
 * The next problem is determined by the recommendation engine
 * (`getNextRecommendation`) which considers difficulty progression,
 * category variety, and SRS review due dates.
 *
 * Design decisions:
 * - The card is styled as `inline-flex` so it flows naturally within the
 *   success banner text without forcing a new block layout.
 * - Difficulty is shown as a color-coded badge so users can gauge the
 *   recommended problem's challenge level at a glance.
 * - Custom problems use a different URL path (`/problems/custom/[slug]`)
 *   than built-in problems (`/problems/[slug]`).
 *
 * @see {@link ProblemSolver} for where recommendations are computed
 * @see {@link getNextRecommendation} for the recommendation algorithm
 */
'use client';

import Link from 'next/link';
import { Badge } from '@/components/ui/badge';
import { Card } from '@/components/ui/card';
import { ArrowRight } from 'lucide-react';
import type { ProblemSummary } from '@/lib/problems/types';
import { DIFFICULTY_COLORS } from '@/lib/ui-constants';

/* ============================================================================
 * Types
 * ============================================================================ */

/**
 * Props for the NextProblemCard component.
 */
interface NextProblemCardProps {
  /** Summary of the next recommended problem to solve */
  problem: ProblemSummary;
}

/* ============================================================================
 * NextProblemCard Component
 * ============================================================================ */

/**
 * Compact card linking to the next recommended problem.
 *
 * Displays the problem title, difficulty badge, and a right-arrow icon
 * as a clickable card that navigates to the problem page.
 *
 * @param props - See {@link NextProblemCardProps}
 * @returns An inline-flex card with a link to the next problem
 */
export function NextProblemCard({ problem }: NextProblemCardProps) {
  // Route to the correct path based on whether this is a custom or built-in problem
  const href = problem.isCustom ? `/problems/custom/${problem.slug}` : `/problems/${problem.slug}`;
  return (
    <Link href={href}>
      <Card className="p-3 hover:bg-muted/50 transition-colors inline-flex items-center gap-3">
        <div className="flex items-center gap-2">
          <span className="text-sm font-medium">Next:</span>
          <span className="text-sm">{problem.title}</span>
          {/* Difficulty badge with color coding from the shared constants */}
          <Badge className={`text-xs ${DIFFICULTY_COLORS[problem.difficulty]}`}>
            {problem.difficulty}
          </Badge>
        </div>
        {/* Right arrow to indicate this is a navigation action */}
        <ArrowRight className="h-4 w-4 text-muted-foreground" />
      </Card>
    </Link>
  );
}
