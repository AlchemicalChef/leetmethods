/**
 * @module problem/index
 *
 * Barrel export file for the problem component suite.
 *
 * Re-exports the primary problem-related components used by route pages.
 * Components not exported here (ProblemSolver, NextProblemCard, CustomProblemForm,
 * PrerequisitesBadge, PrerequisitesPanel) are either page-level components
 * imported directly by route files, or internal sub-components imported by
 * their parent components.
 *
 * Exported components:
 * - {@link ProblemDescription} -- Full problem description panel (metadata, hints, solution)
 * - {@link ProblemList} -- Filterable/sortable problem list (presentational)
 * - {@link ProblemListWithProgress} -- Store-connected ProblemList wrapper
 */
export { ProblemDescription } from './ProblemDescription';
export { ProblemList } from './ProblemList';
export { ProblemListWithProgress } from './ProblemListWithProgress';
