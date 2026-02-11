/**
 * Type definitions for the problem system.
 *
 * Defines the core data structures for Coq problems in LeetMethods. These types
 * are used across the entire application: by the problem loader, the problem
 * solver UI, the stats system, the recommendation engine, the achievement
 * system, and the learning paths.
 *
 * Two representations exist:
 * - `Problem`: The full problem definition with all fields needed for solving
 *   (description, hints, Coq code template, solution, etc.).
 * - `ProblemSummary`: A lightweight projection with just the metadata needed
 *   for listing, filtering, and statistics.
 *
 * Problem JSON files in `src/content/problems/` must conform to the `Problem`
 * interface. The `template` field should end with `Admitted.` so the forbidden
 * tactic detector can catch unmodified submissions.
 *
 * @module problems/types
 */

/* ============================================================================
 * Enumerations
 * ========================================================================= */

/**
 * Problem difficulty level.
 *
 * Determines the color badge displayed on problem cards and is used by the
 * recommendation engine to suggest progressively harder problems.
 * Maps to numeric ordering via `DIFFICULTY_ORDER` in `ui-constants.ts`.
 */
export type Difficulty = 'easy' | 'medium' | 'hard';

/**
 * Problem category (topic area).
 *
 * Each problem belongs to exactly one category. Categories are used for:
 * - Filtering on the problems list page
 * - Category mastery achievements
 * - Statistics breakdown
 * - Recommendation engine (prefer same-category recommendations)
 *
 * The display labels and colors for categories are defined in `ui-constants.ts`.
 */
export type Category = 'logic' | 'induction' | 'lists' | 'data-structures' | 'relations' | 'arithmetic' | 'booleans';

/* ============================================================================
 * Full Problem Definition
 * ========================================================================= */

/**
 * Complete definition of a Coq proof problem.
 *
 * This is the full data structure loaded from JSON files in `src/content/problems/`.
 * It contains everything needed to present the problem to the user, verify their
 * solution, and provide hints.
 *
 * @property id - Unique identifier for the problem (typically matches the slug).
 * @property slug - URL-safe identifier used in routing (`/problems/[slug]`).
 * @property title - Human-readable problem title displayed in the header.
 * @property difficulty - Difficulty classification for badges and sorting.
 * @property category - Topic category for filtering and achievement tracking.
 * @property tags - Free-form tags for additional categorization (e.g., specific
 *                  tactics used: 'induction', 'rewrite', 'destruct').
 * @property description - Full problem description shown in the problem panel.
 *                         Supports the markdown-like formatting from `format-text.tsx`.
 * @property hints - Ordered array of hint strings. Users reveal hints progressively
 *                   (first hint, then second, etc.). The `hintsUsed` count in
 *                   progress affects achievement eligibility.
 * @property prelude - Coq code prepended before the user's code. Contains imports,
 *                     helper definitions, and `Require Import` statements needed
 *                     for the problem. Not shown in the editor.
 * @property template - Initial Coq code shown in the editor. Should end with
 *                      `Admitted.` so the forbidden tactic detector catches
 *                      unmodified submissions.
 * @property solution - Reference solution for the problem. Used for development
 *                      and testing purposes (not shown to users in the UI).
 * @property forbiddenTactics - Array of tactic names that are not allowed in the
 *                              user's solution (e.g., 'Admitted', 'admit'). The
 *                              verifier checks for these before sending code to Coq.
 * @property prerequisites - Optional prerequisite declarations. Problems can
 *                           require completion of other problems and/or knowledge
 *                           of specific concepts. Advisory only (not blocking).
 */
export interface Problem {
  id: string;
  slug: string;
  title: string;
  difficulty: Difficulty;
  category: Category;
  tags: string[];
  description: string;
  hints: string[];
  prelude: string;
  template: string;
  solution: string;
  forbiddenTactics: string[];
  prerequisites?: {
    problems?: string[];
    concepts?: string[];
  };
}

/* ============================================================================
 * Problem Summary (Lightweight Projection)
 * ========================================================================= */

/**
 * Lightweight problem metadata for listing, filtering, and statistics.
 *
 * Contains only the fields needed for the problems index page, recommendation
 * engine, and stats computation. Avoids carrying the heavy `description`,
 * `hints`, `template`, `solution`, and `prelude` fields that are only needed
 * on the individual problem solver page.
 *
 * @property id - Unique problem identifier.
 * @property slug - URL-safe identifier for routing.
 * @property title - Display title for problem cards.
 * @property difficulty - Difficulty level for badge display and sorting.
 * @property category - Topic category for filtering.
 * @property tags - Free-form tags for search and categorization.
 * @property isCustom - Optional flag indicating this is a user-created custom
 *                      problem (not from the built-in problem registry). Custom
 *                      problems are excluded from official statistics and
 *                      achievement calculations.
 */
export interface ProblemSummary {
  id: string;
  slug: string;
  title: string;
  difficulty: Difficulty;
  category: Category;
  tags: string[];
  isCustom?: boolean;
}
