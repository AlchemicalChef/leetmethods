/**
 * @module ProblemsPage
 *
 * Server-rendered page for the `/problems` route -- the main problem browser.
 *
 * This page displays all built-in Coq proof problems in a filterable,
 * sortable list. It is the primary entry point for users who want to
 * browse and select problems to solve.
 *
 * Architecture notes:
 * - This is a **server component** that loads problem data synchronously
 *   at render time using two loaders from `@/lib/problems/loader`:
 *     - `getProblemSummaries()` returns lightweight summaries (id, slug,
 *       title, difficulty, category, tags) used for list rendering.
 *     - `getAllProblems()` returns full problem definitions including
 *       templates, preludes, and solutions. Both are passed to the
 *       `ProblemListWithProgress` client component.
 * - The `ProblemListWithProgress` client component combines server-provided
 *   problem data with client-side progress from the Zustand `progressStore`
 *   to show completion badges, filter controls, and sorting options.
 * - Passing both `problems` (summaries) and `fullProblems` allows the
 *   client component to use summaries for display while accessing full
 *   problem data when needed (e.g., for preview or search features).
 */

import { getAllProblems, getProblemSummaries } from '@/lib/problems/loader';
import { ProblemListWithProgress } from '@/components/problem/ProblemListWithProgress';
import type { Metadata } from 'next';

/**
 * Static page metadata for the problems listing.
 * Overrides the root layout default for this route.
 */
export const metadata: Metadata = {
  title: 'Problems - LeetMethods',
  description: 'Browse and solve Coq proof problems organized by difficulty and category',
};

/**
 * Problems listing page component.
 *
 * Fetches all problem data on the server and passes it to the interactive
 * `ProblemListWithProgress` client component for rendering with progress
 * indicators, filtering, and sorting.
 *
 * @returns The problems page with a heading and the full problem list.
 */
export default function ProblemsPage() {
  const problems = getProblemSummaries();
  const fullProblems = getAllProblems();

  return (
    <div className="max-w-4xl mx-auto px-4 py-8">
      <h1 className="text-3xl font-bold mb-6">Problems</h1>
      <ProblemListWithProgress problems={problems} fullProblems={fullProblems} />
    </div>
  );
}
