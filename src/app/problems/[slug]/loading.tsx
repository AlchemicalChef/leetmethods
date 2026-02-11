/**
 * @module ProblemLoading
 *
 * Next.js App Router loading UI for the `/problems/[slug]` route segment.
 *
 * This component is displayed as a Suspense fallback while the problem page
 * is loading (e.g., during static page generation hydration or when
 * navigating between problems via client-side routing).
 *
 * Unlike the root `loading.tsx` which shows a skeleton layout, this loading
 * state shows a centered spinner with a "Loading problem..." message. The
 * spinner is a simple CSS-animated circle using Tailwind's `animate-spin`
 * utility. The full-height layout (`100vh - 64px`) accounts for the navbar
 * height to vertically center the spinner in the remaining viewport.
 *
 * @returns A vertically centered spinner with loading text.
 */
export default function ProblemLoading() {
  return (
    <div className="h-[calc(100vh-64px)] flex items-center justify-center">
      <div className="flex items-center gap-3 text-muted-foreground">
        {/* Spinning circle indicator -- border-t-transparent creates the gap */}
        <div className="animate-spin rounded-full h-5 w-5 border-2 border-primary border-t-transparent" />
        <span>Loading problem...</span>
      </div>
    </div>
  );
}
