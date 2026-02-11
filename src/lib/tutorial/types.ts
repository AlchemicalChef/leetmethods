/**
 * @module TutorialTypes
 *
 * Shared type definitions for the tutorial system.
 *
 * This module defines the core `TutorialStep` interface that describes a
 * single step within an interactive tutorial. It is imported by:
 *   - All tutorial step definition files (e.g., `tutorial-steps.ts`,
 *     `applied-methods-steps.ts`, etc.) to type their exported arrays.
 *   - The `TutorialConfig` interface in `registry.ts` for the `steps` field.
 *   - The `TutorialPage` component to render step content.
 *
 * This type lives in its own file (rather than being co-located with
 * `registry.ts` or `tutorial-steps.ts`) to avoid circular dependencies:
 * step definition files need the type but should not import the registry,
 * and the registry imports from step definition files.
 *
 * Re-exported from `tutorial-steps.ts` for backward compatibility with
 * older import paths.
 */

/**
 * Represents a single step in an interactive Coq tutorial.
 *
 * Each step presents the user with an explanation of a concept, a Coq
 * exercise to complete, and feedback for both success and struggle cases.
 * Steps are displayed sequentially in the `TutorialPage` component.
 *
 * @property id - Unique numeric identifier for the step within its
 *   tutorial. Used as a stable key for rendering and progress tracking.
 *   By convention, IDs are 1-indexed and sequential.
 *
 * @property title - Short heading displayed at the top of the step
 *   (e.g., "Welcome to Coq", "The intros Tactic"). Should be concise
 *   enough to fit in a navigation breadcrumb.
 *
 * @property explanation - Markdown-formatted instructional text explaining
 *   the concept covered in this step. Supports bold (`**text**`), inline
 *   code (`` `code` ``), and code blocks. Rendered by the
 *   `FormattedDescription` component.
 *
 * @property exercise - The Coq proof exercise for this step, consisting of:
 *   - `prelude`: Coq code prepended before the user's code (imports,
 *     helper definitions). Invisible to the user in the editor but
 *     executed by jsCoq before the template.
 *   - `template`: The initial code shown in the editor. Typically contains
 *     a theorem statement with `Admitted.` as the placeholder proof that
 *     the user must replace with actual tactics.
 *   - `solution`: The complete correct proof, used for the "Show Solution"
 *     feature. Must end with `Qed.` (not `Admitted.`).
 *
 * @property successMessage - Text displayed in a success banner when the
 *   user's proof is verified as complete (no remaining goals). Should
 *   reinforce what the user learned and encourage them to continue.
 *
 * @property hint - Text displayed when the user clicks the "Show Hint"
 *   button. Should provide a helpful nudge without giving away the full
 *   solution (e.g., "Try using the `intros` tactic first").
 */
export interface TutorialStep {
  id: number;
  title: string;
  explanation: string;
  exercise: {
    prelude: string;
    template: string;
    solution: string;
  };
  successMessage: string;
  hint: string;
}
