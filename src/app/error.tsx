/**
 * @module ErrorBoundary
 *
 * Next.js App Router error boundary for the root route segment.
 *
 * This component is automatically rendered by Next.js when an unhandled
 * exception is thrown during rendering of any page that does not have a
 * more specific `error.tsx` closer to it in the route tree.
 *
 * It must be a **client component** ('use client') because error boundaries
 * need to use React's `useEffect`-based error recovery, and Next.js requires
 * the `reset` callback to re-render the segment tree on the client.
 *
 * Design decisions:
 * - Displays the error's `message` if available, otherwise shows a generic
 *   fallback string. This avoids leaking internal stack traces while still
 *   giving the user a meaningful clue about what went wrong.
 * - The `reset` function (provided by Next.js) re-renders the route segment
 *   without a full page reload. This is useful for transient errors such as
 *   network failures or temporary state corruption.
 * - The `digest` property on the error object is a Next.js internal hash
 *   used for deduplicating server-side errors in production; it is not
 *   displayed to the user.
 */
'use client';

/**
 * Global error boundary component.
 *
 * @param props.error - The caught Error object. May include a `digest` string
 *   added by Next.js for server-side error deduplication.
 * @param props.reset - Callback that re-renders the errored route segment,
 *   allowing the user to retry without a full navigation.
 * @returns A centered error message with a "Try again" button.
 */
export default function Error({
  error,
  reset,
}: {
  error: Error & { digest?: string };
  reset: () => void;
}) {
  return (
    <div className="max-w-2xl mx-auto px-4 py-20 text-center">
      <h2 className="text-2xl font-bold mb-4">Something went wrong</h2>
      <p className="text-muted-foreground mb-6">
        {error.message || 'An unexpected error occurred.'}
      </p>
      <button
        onClick={reset}
        className="px-4 py-2 text-sm font-medium rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors"
      >
        Try again
      </button>
    </div>
  );
}
