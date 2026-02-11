/**
 * @module CoqStatusBar
 *
 * A shared status bar component that displays the jsCoq initialization state.
 *
 * This component is used by both ProblemSolver and TutorialPage to show:
 * - A loading spinner with "Initializing Coq runtime..." during jsCoq startup
 * - An error message if jsCoq initialization fails
 *
 * The bar automatically hides itself (returns null) when there is neither a
 * loading state nor an error, keeping the UI clean once Coq is ready.
 *
 * Design decisions:
 * - The component is intentionally simple and stateless -- it purely reflects
 *   the loading/error props from the parent's `useCoqSession` hook.
 * - Uses a compact single-line layout (border-b, small text) so it can sit
 *   unobtrusively above the editor toolbar without taking significant space.
 * - The error message has a title attribute for the full text, since long
 *   initialization errors might be truncated in the compact bar.
 * - An optional `errorPrefix` prop allows parents to prepend context like
 *   "Failed to initialize Coq: " before the actual error string.
 *
 * @see {@link ProblemSolver} which uses this with errorPrefix
 * @see {@link TutorialPage} which also uses this component
 * @see {@link useCoqSession} which provides the loading/error state
 */
import { Loader2, AlertCircle } from 'lucide-react';

/**
 * Props for the CoqStatusBar component.
 */
interface CoqStatusBarProps {
  /** Whether jsCoq is currently initializing (loading .vo libraries, etc.) */
  loading: boolean;
  /** Error message if initialization failed, or null if no error */
  error: string | null;
  /** Optional prefix prepended to the error message for context */
  errorPrefix?: string;
}

/**
 * Compact status bar showing jsCoq initialization progress or errors.
 *
 * Returns null when neither loading nor error, so it occupies no space
 * once Coq is successfully initialized.
 *
 * @param props - See {@link CoqStatusBarProps}
 * @returns Status bar element, or null if nothing to show
 */
export function CoqStatusBar({ loading, error, errorPrefix }: CoqStatusBarProps) {
  // Hide entirely when there is nothing to display
  if (!loading && !error) return null;

  return (
    <div className="flex items-center gap-2 px-3 py-2 border-b bg-muted/20 text-xs">
      {loading ? (
        <>
          {/* Spinning loader during jsCoq initialization */}
          <Loader2 className="h-3 w-3 animate-spin text-muted-foreground" />
          <span className="text-muted-foreground">Initializing Coq runtime...</span>
        </>
      ) : error ? (
        <>
          {/* Error icon and message when initialization fails */}
          <AlertCircle className="h-3 w-3 text-destructive" />
          <span className="text-destructive" title={error}>
            {errorPrefix}{error}
          </span>
        </>
      ) : null}
    </div>
  );
}
