/**
 * @module PrerequisitesBadge
 *
 * A small amber badge that shows the count of unsatisfied prerequisites
 * for a problem in the problem list view.
 *
 * This badge appears next to problem cards in the ProblemList component
 * to warn users that certain problems or concepts should be completed
 * before attempting the problem. The badge is intentionally compact --
 * the full prerequisite details are shown on the problem's own page
 * via the PrerequisitesPanel component.
 *
 * Design decisions:
 * - Returns null when count is 0 to avoid rendering empty badges.
 * - Uses amber/warning coloring to indicate "recommended but not blocking"
 *   -- users can still attempt problems with unmet prerequisites.
 * - Pluralizes "prereq" vs "prereqs" for grammatical correctness.
 * - Uses the AlertTriangle icon for visual consistency with the
 *   PrerequisitesPanel which uses the same icon.
 *
 * @see {@link PrerequisitesPanel} for the detailed prerequisites display
 * @see {@link ProblemList} for where this badge is rendered
 */
'use client';

import { Badge } from '@/components/ui/badge';
import { AlertTriangle } from 'lucide-react';

/* ============================================================================
 * Types
 * ============================================================================ */

/**
 * Props for the PrerequisitesBadge component.
 */
interface PrerequisitesBadgeProps {
  /** Number of unsatisfied prerequisites (0 = all met, badge is hidden) */
  unsatisfiedCount: number;
}

/* ============================================================================
 * PrerequisitesBadge Component
 * ============================================================================ */

/**
 * Compact badge showing the count of unsatisfied prerequisites.
 *
 * Returns null when all prerequisites are satisfied (count === 0).
 *
 * @param props - See {@link PrerequisitesBadgeProps}
 * @returns An amber badge with the prerequisite count, or null if all met
 */
export function PrerequisitesBadge({ unsatisfiedCount }: PrerequisitesBadgeProps) {
  // Don't render anything when all prerequisites are satisfied
  if (unsatisfiedCount === 0) return null;

  return (
    <Badge
      variant="outline"
      className="bg-amber-50 text-amber-700 border-amber-200 dark:bg-amber-950/30 dark:text-amber-400 dark:border-amber-800"
    >
      <AlertTriangle className="h-3 w-3 mr-1" />
      {/* Pluralize "prereq" based on count */}
      {unsatisfiedCount} prereq{unsatisfiedCount !== 1 ? 's' : ''}
    </Badge>
  );
}
