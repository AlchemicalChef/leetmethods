/**
 * @module NotFound
 *
 * Custom 404 page for the LeetMethods application.
 *
 * This component is rendered by Next.js whenever:
 *   - A user navigates to a URL that does not match any defined route.
 *   - A page or layout explicitly calls `notFound()` from 'next/navigation'
 *     (e.g., when a problem slug does not exist in the problem registry).
 *
 * The page provides a simple, centered "404" message with a link back to the
 * home page. It uses Next.js's `Link` component for client-side navigation
 * to avoid a full page reload when the user clicks "Go Home".
 *
 * This is a **server component** -- no client-side interactivity is required.
 *
 * @returns A centered 404 error page with a navigation link to the home page.
 */
import Link from 'next/link';

export default function NotFound() {
  return (
    <div className="max-w-2xl mx-auto px-4 py-20 text-center">
      <h2 className="text-4xl font-bold mb-4">404</h2>
      <p className="text-muted-foreground mb-6">
        The page you&apos;re looking for doesn&apos;t exist.
      </p>
      <Link
        href="/"
        className="px-4 py-2 text-sm font-medium rounded-md bg-primary text-primary-foreground hover:bg-primary/90 transition-colors inline-block"
      >
        Go Home
      </Link>
    </div>
  );
}
