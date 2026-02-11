/**
 * @module PrerequisitesPanel
 *
 * Displays the detailed prerequisite status for a problem, showing which
 * prerequisite problems and concepts have been completed and which remain.
 *
 * This panel appears in the ProblemDescription component when a problem has
 * defined prerequisites. It shows two sections:
 *
 * 1. **Problem prerequisites** -- Other problems that should be solved first.
 *    Each is a link to the prerequisite problem page, with a check/circle icon
 *    indicating completion status.
 *
 * 2. **Concept prerequisites** -- Conceptual knowledge areas (e.g., "induction",
 *    "pattern matching") that link to learning resources or relevant problems.
 *    Each shows its satisfaction status and optional description.
 *
 * Design decisions:
 * - The panel uses amber/warning styling to indicate "recommended but not blocking."
 *   Prerequisites are advisory -- users can still attempt the problem.
 * - Completed prerequisites are shown with a green checkmark and line-through
 *   text styling to visually de-emphasize them.
 * - When all prerequisites are met, a small "All met" indicator appears in the
 *   header to provide positive reinforcement.
 * - Concept prerequisite links support both absolute paths (starting with '/')
 *   and problem slugs (prefixed with '/problems/') for flexibility.
 * - Concept descriptions are hidden on small screens to save space.
 *
 * @see {@link ProblemDescription} for the parent component
 * @see {@link PrerequisitesBadge} for the compact badge used in ProblemList
 * @see {@link getPrerequisiteStatus} for the computation of prerequisite status
 */
'use client';

import Link from 'next/link';
import { Card } from '@/components/ui/card';
import { CheckCircle2, Circle, BookOpen, AlertTriangle } from 'lucide-react';
import type { PrerequisiteStatus } from '@/lib/prerequisites';

/* ============================================================================
 * Types
 * ============================================================================ */

/**
 * Props for the PrerequisitesPanel component.
 */
interface PrerequisitesPanelProps {
  /** Prerequisite status object containing problem and concept prereqs with satisfaction data */
  status: PrerequisiteStatus;
}

/* ============================================================================
 * PrerequisitesPanel Component
 * ============================================================================ */

/**
 * Detailed prerequisites panel showing problem and concept requirements.
 *
 * Returns null if there are no prerequisites of either type.
 *
 * @param props - See {@link PrerequisitesPanelProps}
 * @returns An amber-themed card with prerequisite checklists, or null if empty
 */
export function PrerequisitesPanel({ status }: PrerequisitesPanelProps) {
  const { problemPrereqs, conceptPrereqs } = status;

  // Don't render if there are no prerequisites
  if (problemPrereqs.length === 0 && conceptPrereqs.length === 0) return null;

  return (
    <Card className="border-amber-200 dark:border-amber-800 bg-amber-50/50 dark:bg-amber-950/20 p-4">
      {/* Panel header with warning icon and optional "All met" indicator */}
      <div className="flex items-center gap-2 mb-3">
        <AlertTriangle className="h-4 w-4 text-amber-600 dark:text-amber-400" />
        <span className="font-medium text-amber-800 dark:text-amber-300">Prerequisites</span>
        {status.allSatisfied && (
          <span className="text-xs text-green-600 dark:text-green-400 ml-auto">All met</span>
        )}
      </div>

      {/* Problem prerequisites section -- links to prerequisite problems */}
      {problemPrereqs.length > 0 && (
        <div className="space-y-1.5 mb-3">
          <span className="text-xs text-amber-700 dark:text-amber-400 font-medium">Problems</span>
          {problemPrereqs.map((p) => (
            <Link
              key={p.slug}
              href={`/problems/${p.slug}`}
              className="flex items-center gap-2 text-sm hover:underline"
            >
              {/* Green check for completed, amber circle for pending */}
              {p.completed ? (
                <CheckCircle2 className="h-3.5 w-3.5 text-green-500 shrink-0" />
              ) : (
                <Circle className="h-3.5 w-3.5 text-amber-400 shrink-0" />
              )}
              {/* Completed prereqs get muted, struck-through text */}
              <span className={p.completed ? 'text-muted-foreground line-through' : 'text-foreground'}>
                {p.title}
              </span>
            </Link>
          ))}
        </div>
      )}

      {/* Concept prerequisites section -- links to learning resources */}
      {conceptPrereqs.length > 0 && (
        <div className="space-y-1.5">
          <span className="text-xs text-amber-700 dark:text-amber-400 font-medium">Concepts</span>
          {conceptPrereqs.map((c) => (
            <Link
              key={c.id}
              href={c.learnPath.startsWith('/') ? c.learnPath : `/problems/${c.learnPath}`}
              className="flex items-center gap-2 text-sm hover:underline"
            >
              {/* Green check for satisfied, amber book icon for unsatisfied */}
              {c.satisfied ? (
                <CheckCircle2 className="h-3.5 w-3.5 text-green-500 shrink-0" />
              ) : (
                <BookOpen className="h-3.5 w-3.5 text-amber-400 shrink-0" />
              )}
              {/* Satisfied concepts get muted, struck-through text */}
              <span className={c.satisfied ? 'text-muted-foreground line-through' : 'text-foreground'}>
                {c.displayName}
              </span>
              {/* Show concept description on larger screens for unsatisfied concepts */}
              {!c.satisfied && c.description && (
                <span className="text-xs text-muted-foreground hidden sm:inline">
                  - {c.description}
                </span>
              )}
            </Link>
          ))}
        </div>
      )}
    </Card>
  );
}
