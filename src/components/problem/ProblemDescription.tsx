/**
 * @module ProblemDescription
 *
 * Renders the full description panel for a Coq proof problem, including
 * metadata, hints, prelude code, prerequisites, and the reference solution.
 *
 * This component occupies the left panel (desktop) or top panel (mobile) of
 * the ProblemSolver layout. It provides all the information the user needs
 * to understand and solve the problem, organized in a scrollable view.
 *
 * Sections (in order):
 * 1. **Title and metadata** -- Problem name, difficulty badge, category, tags
 * 2. **Custom problem actions** -- Edit/Delete buttons (for user-created problems)
 * 3. **Prerequisites** -- Which problems/concepts must be completed first
 * 4. **Description** -- Rendered via FormattedDescription (markdown-like formatting)
 * 5. **Hints** -- Progressive reveal; tracks how many the user has uncovered
 * 6. **Prelude** -- Collapsible view of read-only imports/definitions
 * 7. **Reference solution** -- Gated behind a confirmation dialog, then collapsible
 *
 * Design decisions:
 * - Hints use progressive reveal to encourage users to think before peeking.
 *   Each reveal is tracked in the progress store for analytics.
 * - The reference solution requires explicit confirmation ("Are you sure?")
 *   to discourage premature viewing. It is only available after completion,
 *   or after 5+ failed attempts (mercy rule).
 * - The prelude section is collapsed by default since most users do not need
 *   to reference it, but advanced users can expand it to see imports/helpers.
 * - Uses FormattedDescription component for description rendering which
 *   supports basic markdown-like formatting and prevents XSS (FIX #2).
 *
 * @see {@link ProblemSolver} for the parent component
 * @see {@link FormattedDescription} for the description text renderer
 * @see {@link PrerequisitesPanel} for the prerequisites display
 */
'use client';

import { useState } from 'react';
import { Badge } from '@/components/ui/badge';
import { Button } from '@/components/ui/button';
import { Card } from '@/components/ui/card';
import { ScrollArea } from '@/components/ui/scroll-area';
import { Separator } from '@/components/ui/separator';
import { ChevronDown, ChevronRight, Lightbulb, BookOpen, Eye } from 'lucide-react';
import type { Problem } from '@/lib/problems/types';
import type { PrerequisiteStatus } from '@/lib/prerequisites';
import { DIFFICULTY_COLORS } from '@/lib/ui-constants';
import { FormattedDescription } from '@/lib/format-text';
import { PrerequisitesPanel } from './PrerequisitesPanel';

/* ============================================================================
 * Types
 * ============================================================================ */

/**
 * Props for the ProblemDescription component.
 */
interface ProblemDescriptionProps {
  /** The full problem object containing all metadata and content */
  problem: Problem;
  /** How many hints have been revealed so far (0-based count) */
  hintsRevealed: number;
  /** Callback to reveal the next hint */
  onRevealHint: () => void;
  /** Whether the reference solution is available to view */
  solutionAvailable?: boolean;
  /** Prerequisite satisfaction status (which prereqs are met/unmet) */
  prerequisiteStatus?: PrerequisiteStatus;
  /** Whether this is a user-created custom problem */
  isCustom?: boolean;
  /** Callback for the Edit button (custom problems only) */
  onEdit?: () => void;
  /** Callback for the Delete button (custom problems only) */
  onDelete?: () => void;
  /** Additional CSS classes for the scroll area container */
  className?: string;
}

/* ============================================================================
 * ProblemDescription Component
 * ============================================================================ */

/**
 * Full problem description panel with metadata, hints, prelude, and solution.
 *
 * @param props - See {@link ProblemDescriptionProps}
 * @returns The scrollable problem description UI
 */
export function ProblemDescription({
  problem,
  hintsRevealed,
  onRevealHint,
  solutionAvailable = false,
  prerequisiteStatus,
  isCustom,
  onEdit,
  onDelete,
  className = '',
}: ProblemDescriptionProps) {
  /** Whether the collapsible prelude section is expanded */
  const [showPrelude, setShowPrelude] = useState(false);

  return (
    <ScrollArea className={`h-full ${className}`}>
      <div className="p-6 space-y-6">
        {/* Section: Title and metadata badges */}
        <div>
          <h1 className="text-2xl font-bold mb-3">{problem.title}</h1>
          <div className="flex flex-wrap gap-2 items-center">
            {/* Difficulty badge with color coding from ui-constants */}
            <Badge className={DIFFICULTY_COLORS[problem.difficulty]}>
              {problem.difficulty.charAt(0).toUpperCase() + problem.difficulty.slice(1)}
            </Badge>
            <Badge variant="outline">{problem.category}</Badge>
            {problem.tags.map((tag) => (
              <Badge key={tag} variant="secondary">
                {tag}
              </Badge>
            ))}
          </div>
        </div>

        {/* Section: Custom problem actions (Edit/Delete) */}
        {isCustom && (onEdit || onDelete) && (
          <div className="flex items-center gap-2">
            {onEdit && (
              <Button variant="outline" size="sm" onClick={onEdit}>
                Edit
              </Button>
            )}
            {onDelete && (
              <Button variant="outline" size="sm" onClick={onDelete} className="text-red-600 hover:text-red-700">
                Delete
              </Button>
            )}
          </div>
        )}

        {/* Section: Prerequisites panel -- only shown if there are any prereqs */}
        {prerequisiteStatus && (prerequisiteStatus.problemPrereqs.length > 0 || prerequisiteStatus.conceptPrereqs.length > 0) && (
          <PrerequisitesPanel status={prerequisiteStatus} />
        )}

        <Separator />

        {/* Section: Problem description -- FIX #2: Sanitize HTML to prevent XSS */}
        <div className="prose prose-sm dark:prose-invert max-w-none">
          <FormattedDescription text={problem.description} />
        </div>

        {/* Section: Progressive hints */}
        {problem.hints.length > 0 && (
          <Card className="p-4">
            <div className="flex items-center gap-2 mb-3">
              <Lightbulb className="h-4 w-4 text-yellow-500" />
              <span className="font-medium">Hints</span>
              <span className="text-sm text-muted-foreground">
                ({hintsRevealed}/{problem.hints.length} revealed)
              </span>
            </div>

            {/* Revealed hints -- shown with a yellow left border for visual grouping */}
            <div className="space-y-2">
              {problem.hints.slice(0, hintsRevealed).map((hint, index) => (
                <div
                  key={index}
                  className="text-sm p-2 bg-muted/50 rounded border-l-2 border-yellow-400"
                >
                  <span className="font-medium text-muted-foreground">Hint {index + 1}:</span>{' '}
                  {hint}
                </div>
              ))}
            </div>

            {/* Reveal next hint button -- hidden when all hints are shown */}
            {hintsRevealed < problem.hints.length && (
              <Button
                variant="ghost"
                size="sm"
                onClick={onRevealHint}
                className="mt-3"
              >
                <Lightbulb className="h-3 w-3 mr-1" />
                Show Hint {hintsRevealed + 1}
              </Button>
            )}
          </Card>
        )}

        {/* Section: Collapsible prelude code (read-only imports/definitions) */}
        {problem.prelude && (
          <Card className="overflow-hidden">
            <button
              onClick={() => setShowPrelude(!showPrelude)}
              aria-label={showPrelude ? 'Hide prelude code' : 'Show prelude code'}
              className="w-full flex items-center gap-2 p-3 hover:bg-muted/50 transition-colors"
            >
              {showPrelude ? (
                <ChevronDown className="h-4 w-4" />
              ) : (
                <ChevronRight className="h-4 w-4" />
              )}
              <BookOpen className="h-4 w-4 text-muted-foreground" />
              <span className="font-medium">Prelude</span>
              <span className="text-sm text-muted-foreground">(read-only imports/definitions)</span>
            </button>

            {showPrelude && (
              <div className="border-t bg-muted/20">
                <pre className="p-4 text-sm font-mono overflow-x-auto">
                  <code>{problem.prelude}</code>
                </pre>
              </div>
            )}
          </Card>
        )}

        {/* Section: Reference solution (gated behind confirmation) */}
        {solutionAvailable && problem.solution && (
          <SolutionReveal solution={problem.solution} />
        )}
      </div>
    </ScrollArea>
  );
}

/* ============================================================================
 * SolutionReveal Sub-component
 * ============================================================================ */

/**
 * Two-phase solution reveal component.
 *
 * Phase 1 (not confirmed): Shows a warning card asking the user to confirm
 * they want to see the solution. This friction is intentional to encourage
 * independent problem-solving.
 *
 * Phase 2 (confirmed): Shows a collapsible card with the reference solution
 * code. The solution starts collapsed so the user can still avoid seeing it
 * even after confirming.
 *
 * @param props.solution - The reference Coq proof solution code
 */
function SolutionReveal({ solution }: { solution: string }) {
  /** Whether the user has confirmed they want to see the solution */
  const [confirmed, setConfirmed] = useState(false);
  /** Whether the solution code block is expanded (only after confirmation) */
  const [expanded, setExpanded] = useState(false);

  /* --- Phase 1: Confirmation prompt --- */
  if (!confirmed) {
    return (
      <Card className="border-amber-200 dark:border-amber-800 bg-amber-50/50 dark:bg-amber-950/20 p-4">
        <div className="flex items-center gap-2 mb-2">
          <Eye className="h-4 w-4 text-amber-600 dark:text-amber-400" />
          <span className="font-medium text-amber-800 dark:text-amber-300">Reference Solution</span>
        </div>
        <p className="text-sm text-amber-700 dark:text-amber-400 mb-3">
          Are you sure you want to see the solution? Try solving it yourself first!
        </p>
        <Button
          variant="outline"
          size="sm"
          onClick={() => setConfirmed(true)}
          className="border-amber-300 dark:border-amber-700 text-amber-800 dark:text-amber-300 hover:bg-amber-100 dark:hover:bg-amber-900/30"
        >
          <Eye className="h-3 w-3 mr-1" />
          Show Solution
        </Button>
      </Card>
    );
  }

  /* --- Phase 2: Collapsible solution view --- */
  return (
    <Card className="border-amber-200 dark:border-amber-800 overflow-hidden">
      <button
        onClick={() => setExpanded(!expanded)}
        aria-label={expanded ? 'Hide reference solution' : 'Show reference solution'}
        className="w-full flex items-center gap-2 p-3 hover:bg-amber-50/50 dark:hover:bg-amber-950/20 transition-colors"
      >
        {expanded ? (
          <ChevronDown className="h-4 w-4 text-amber-600" />
        ) : (
          <ChevronRight className="h-4 w-4 text-amber-600" />
        )}
        <Eye className="h-4 w-4 text-amber-600 dark:text-amber-400" />
        <span className="font-medium text-amber-800 dark:text-amber-300">Reference Solution</span>
      </button>
      {expanded && (
        <div className="border-t border-amber-200 dark:border-amber-800 bg-muted/20">
          <pre className="p-4 text-sm font-mono overflow-x-auto">
            <code>{solution}</code>
          </pre>
        </div>
      )}
    </Card>
  );
}
