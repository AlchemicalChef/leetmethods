/**
 * @module RootLoading
 *
 * Next.js App Router loading UI for the root route segment.
 *
 * This component is displayed automatically by Next.js as a fallback while
 * the main page content (or any nested layout/page without its own
 * `loading.tsx`) is being loaded via React Suspense.
 *
 * The skeleton layout mimics the general shape of a typical content page:
 *   - A wide heading placeholder (48px tall, 192px wide)
 *   - A narrower subtitle placeholder (16px tall, 288px wide)
 *   - Three tall card/row placeholders (80px each) representing list items
 *
 * All placeholders use the `animate-pulse` Tailwind utility to create a
 * subtle shimmer effect, signaling to the user that content is loading.
 *
 * This is a **server component** (no 'use client' directive needed) since it
 * renders only static skeleton HTML with no interactivity.
 *
 * @returns A pulsing skeleton placeholder layout.
 */
export default function Loading() {
  return (
    <div className="max-w-4xl mx-auto px-4 py-12">
      <div className="animate-pulse space-y-4">
        {/* Heading skeleton */}
        <div className="h-8 bg-muted rounded w-48" />
        {/* Subtitle skeleton */}
        <div className="h-4 bg-muted rounded w-72" />
        {/* List item skeletons -- three rows to approximate typical page content */}
        <div className="space-y-3 mt-8">
          {[1, 2, 3].map((i) => (
            <div key={i} className="h-20 bg-muted rounded" />
          ))}
        </div>
      </div>
    </div>
  );
}
