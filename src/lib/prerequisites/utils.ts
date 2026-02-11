/**
 * Prerequisite evaluation utilities for the problem system.
 *
 * Problems in LeetMethods can declare two kinds of prerequisites:
 * 1. **Problem prerequisites**: Other problems that should be completed first
 *    (e.g., "plus-n-zero" should be completed before "plus-comm").
 * 2. **Concept prerequisites**: Tactics, lemmas, or concepts the user should
 *    understand (e.g., 'tactic:induction', 'lemma:add_0_r').
 *
 * This module evaluates which prerequisites are satisfied and which are not,
 * providing data for the prerequisite panel UI that warns users when they
 * are attempting a problem without the expected background knowledge.
 *
 * Prerequisites are advisory, not blocking -- users can always attempt any
 * problem regardless of prerequisite status. The UI simply shows a helpful
 * warning with links to learn the missing concepts.
 *
 * @module prerequisites/utils
 */

import type { Problem } from '@/lib/problems/types';
import { conceptMap } from './concepts';
import type { ConceptInfo } from './concepts';

/* ============================================================================
 * Type Definitions
 * ========================================================================= */

/**
 * Status of a single problem prerequisite.
 *
 * @property slug - The prerequisite problem's slug.
 * @property title - Display title of the prerequisite problem (falls back to
 *                   the slug if the problem is not found in the registry).
 * @property completed - Whether the user has completed this prerequisite problem.
 */
export interface ProblemPrereq {
  slug: string;
  title: string;
  completed: boolean;
}

/**
 * Status of a single concept prerequisite.
 *
 * @property id - The concept ID (e.g., 'tactic:intros').
 * @property displayName - Human-readable name for the concept.
 * @property description - Brief explanation of the concept.
 * @property satisfied - Whether this concept prerequisite is considered met.
 *                       Tutorial-linked concepts are always satisfied (tutorials
 *                       are freely accessible). Problem-linked concepts are
 *                       satisfied when the associated problem is completed.
 * @property learnPath - URL or problem slug where the user can learn this concept.
 */
export interface ConceptPrereq {
  id: string;
  displayName: string;
  description: string;
  satisfied: boolean;
  learnPath: string;
}

/**
 * Combined prerequisite status for a problem, including both problem
 * and concept prerequisites.
 *
 * @property problemPrereqs - Array of problem prerequisite statuses.
 * @property conceptPrereqs - Array of concept prerequisite statuses.
 * @property allSatisfied - `true` if every prerequisite (both problem and concept)
 *                          is satisfied. Used by the UI to decide whether to show
 *                          the prerequisites warning panel.
 */
export interface PrerequisiteStatus {
  problemPrereqs: ProblemPrereq[];
  conceptPrereqs: ConceptPrereq[];
  allSatisfied: boolean;
}

/* ============================================================================
 * Prerequisite Evaluation
 * ========================================================================= */

/**
 * Evaluates the prerequisite status for a given problem.
 *
 * Cross-references the problem's declared prerequisites against the user's
 * completed problems and the concept registry. Returns a structured status
 * object that the UI can render directly.
 *
 * Concept satisfaction rules:
 * - If the concept's `learnPath` starts with '/' (a tutorial URL), the concept
 *   is always considered satisfied because tutorials are freely accessible.
 * - If the concept's `learnPath` is a problem slug, the concept is satisfied
 *   only when that problem has been completed.
 *
 * @param problem - The problem whose prerequisites to evaluate.
 * @param completedSlugs - Array of problem slugs the user has completed.
 * @param allProblems - The full list of problems (used to look up titles
 *                      for problem prerequisites).
 * @returns A `PrerequisiteStatus` object with the evaluation results.
 */
export function getPrerequisiteStatus(
  problem: Problem,
  completedSlugs: string[],
  allProblems: Problem[]
): PrerequisiteStatus {
  const completed = new Set(completedSlugs);
  const problemMap = new Map(allProblems.map((p) => [p.slug, p]));

  /**
   * Evaluate problem prerequisites: check if each required problem slug
   * is in the completed set. Falls back to the slug as the title if
   * the problem is not found (handles removed/renamed problems gracefully).
   */
  const problemPrereqs: ProblemPrereq[] = (problem.prerequisites?.problems ?? []).map((slug) => {
    const p = problemMap.get(slug);
    return {
      slug,
      title: p?.title ?? slug,
      completed: completed.has(slug),
    };
  });

  /**
   * Evaluate concept prerequisites: look up each concept ID in the
   * concept registry and determine satisfaction based on the concept's
   * learn path type.
   */
  const conceptPrereqs: ConceptPrereq[] = (problem.prerequisites?.concepts ?? []).map((conceptId) => {
    const concept: ConceptInfo | undefined = conceptMap.get(conceptId);

    /**
     * Determine if this concept prerequisite is satisfied:
     * - Tutorial links (paths starting with '/') are always considered satisfied
     *   because tutorials are freely accessible without completing any problems.
     * - Problem-linked concepts are satisfied when the referenced problem is completed.
     */
    let satisfied = false;
    if (concept) {
      if (concept.learnPath.startsWith('/')) {
        satisfied = true;
      } else {
        satisfied = completed.has(concept.learnPath);
      }
    }
    return {
      id: conceptId,
      displayName: concept?.displayName ?? conceptId,
      description: concept?.description ?? '',
      satisfied,
      learnPath: concept?.learnPath ?? '#',
    };
  });

  /**
   * All prerequisites are satisfied when every problem prerequisite is
   * completed AND every concept prerequisite is satisfied.
   */
  const allSatisfied =
    problemPrereqs.every((p) => p.completed) &&
    conceptPrereqs.every((c) => c.satisfied);

  return { problemPrereqs, conceptPrereqs, allSatisfied };
}

/**
 * Counts the total number of unsatisfied prerequisites.
 *
 * Used by the UI to display a badge count (e.g., "3 prerequisites not met")
 * on the problem page.
 *
 * @param status - A previously computed `PrerequisiteStatus` object.
 * @returns The total count of unsatisfied problem and concept prerequisites.
 */
export function getUnsatisfiedCount(status: PrerequisiteStatus): number {
  const unsatisfiedProblems = status.problemPrereqs.filter((p) => !p.completed).length;
  const unsatisfiedConcepts = status.conceptPrereqs.filter((c) => !c.satisfied).length;
  return unsatisfiedProblems + unsatisfiedConcepts;
}
