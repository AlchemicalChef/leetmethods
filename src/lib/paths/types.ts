/**
 * Type definitions for the learning paths system.
 *
 * Learning paths are curated sequences of problems that guide users through
 * a specific topic area (e.g., boolean basics, induction, relations). These
 * types define the shape of path and step data, and are used throughout the
 * paths module (`loader.ts`, `paths.ts`, `progress.ts`) and the `/learn` page UI.
 *
 * The types are kept in a separate file to avoid circular imports, since both
 * the path data (`paths.ts`) and the progress computation (`progress.ts`) need
 * to reference them.
 *
 * @module paths/types
 */

/* ============================================================================
 * Type Definitions
 * ========================================================================= */

/**
 * A single step within a learning path.
 *
 * Each step corresponds to one problem that the user should complete as part
 * of the path. The step's `title` and `description` provide path-specific
 * context that may differ from the problem's own title and description.
 *
 * @property problemSlug - The slug of the problem to solve for this step.
 *                         Must match a slug registered in the problem loader.
 * @property title - Display title for the step within the path context.
 * @property description - Brief explanation of what the user will learn or
 *                         practice in this step.
 */
export interface PathStep {
  problemSlug: string;
  title: string;
  description: string;
}

/**
 * A complete learning path definition.
 *
 * Paths are displayed on the `/learn` page and provide a structured way
 * for users to progress through related problems in a logical order.
 *
 * @property slug - Unique URL-safe identifier for the path (e.g., 'boolean-basics').
 *                  Used in routing and progress tracking.
 * @property title - Human-readable name displayed in the path card header.
 * @property description - Multi-sentence explanation of what the path covers
 *                         and what the user will learn.
 * @property difficulty - Difficulty tier for display and filtering. Determines
 *                        the color badge shown on the path card.
 * @property icon - Emoji string used as the visual icon on the path card.
 * @property steps - Ordered array of path steps. The user is expected to
 *                   complete them in sequence, though any step can be
 *                   attempted at any time.
 */
export interface LearningPath {
  slug: string;
  title: string;
  description: string;
  difficulty: 'beginner' | 'intermediate' | 'advanced';
  icon: string;
  steps: PathStep[];
}
