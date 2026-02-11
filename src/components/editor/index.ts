/**
 * @module editor/index
 *
 * Barrel export file for the editor component suite.
 *
 * Re-exports the core editor components used by ProblemSolver, TutorialPage,
 * and other pages that need the Coq editing experience. Components not exported
 * here (GuidedProofPanel, KeyboardShortcutsHelp) are internal to the editor
 * module and imported directly by the components that need them.
 *
 * Exported components:
 * - {@link CoqEditor} -- CodeMirror 6 editor with Coq syntax highlighting
 * - {@link GoalsPanel} -- Proof goals, hypotheses, and messages display
 * - {@link EditorToolbar} -- Execution controls (step, run, reset, submit)
 * - {@link CoqStatusBar} -- jsCoq initialization loading/error indicator
 */
export { CoqEditor } from './CoqEditor';
export { GoalsPanel } from './GoalsPanel';
export { EditorToolbar } from './EditorToolbar';
export { CoqStatusBar } from './CoqStatusBar';
