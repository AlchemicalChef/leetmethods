/**
 * @module LearnPage
 *
 * Server-rendered page for the `/learn` route -- the Learning Paths hub.
 *
 * Learning Paths are curated sequences of problems organized into a
 * progressive curriculum (e.g., "Beginner Logic", "Induction Mastery").
 * This page serves as the entry point where users can browse available
 * paths and see their overall progress.
 *
 * Architecture notes:
 * - This is a **server component** that fetches problem summaries
 *   synchronously via `getProblemSummaries()` and passes them to the
 *   client-side `LearnHub` component. The summaries contain only the
 *   lightweight fields (id, slug, title, difficulty, category, tags)
 *   needed to display path step listings without loading full problem
 *   definitions (which include templates, preludes, and solutions).
 * - The `LearnHub` client component handles interactive state such as
 *   reading user progress from the Zustand `progressStore` (persisted
 *   in localStorage) and computing per-path completion percentages.
 * - Page metadata is exported statically for SEO and browser tab titles.
 */

import type { Metadata } from 'next';
import { LearnHub } from '@/components/learn/LearnHub';
import { getProblemSummaries } from '@/lib/problems/loader';

/**
 * Static metadata for the Learn page. Overrides the root layout's default
 * title and description for this specific route.
 */
export const metadata: Metadata = {
  title: 'Learn Coq | LeetMethods',
  description: 'A gentle introduction to theorem proving with Coq. Follow guided learning paths from beginner to advanced.',
};

/**
 * Learn hub page component.
 *
 * Loads all problem summaries on the server and delegates rendering to
 * the interactive `LearnHub` client component, which combines server-provided
 * problem data with client-side progress state.
 *
 * @returns The Learn page layout with heading, description, and the LearnHub component.
 */
export default function LearnPage() {
  const problems = getProblemSummaries();

  return (
    <div className="max-w-4xl mx-auto px-4 py-12">
      <h1 className="text-4xl font-bold mb-4">Learn Coq</h1>
      <p className="text-xl text-muted-foreground mb-8">
        A gentle introduction to theorem proving with Coq
      </p>
      <LearnHub problems={problems} />
    </div>
  );
}
