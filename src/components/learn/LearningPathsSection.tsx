/**
 * @module LearningPathsSection
 *
 * Section component that renders the "Learning Paths" area on the Learn page.
 *
 * This component loads all available learning paths via `getAllPaths()` and
 * displays them in a responsive grid of PathCard components. Each PathCard
 * shows the path's metadata and the user's progress through it.
 *
 * Design decisions:
 *   - `getAllPaths()` is a synchronous function (static imports) so this
 *     component does not need loading states or suspense boundaries.
 *   - The grid layout uses 1 column on small screens, 2 on medium, and 3
 *     on large screens to optimize readability at each breakpoint.
 *   - Each PathCard is keyed by the path's slug, which is unique across all
 *     learning paths.
 */
'use client';

import { getAllPaths } from '@/lib/paths/loader';
import { PathCard } from './PathCard';

/**
 * Renders the Learning Paths section with a heading, description, and
 * a responsive grid of PathCard components.
 *
 * @returns The learning paths section UI.
 */
export function LearningPathsSection() {
  /* Load all learning paths synchronously. The paths loader uses static
     imports so this is always available without async/await. */
  const paths = getAllPaths();

  return (
    <div>
      {/* Section heading and description */}
      <h2 className="text-2xl font-semibold mb-2">Learning Paths</h2>
      <p className="text-muted-foreground mb-4">Follow guided sequences to build your skills</p>

      {/* Responsive grid of path cards.
          Columns: 1 (mobile) -> 2 (md: 768px+) -> 3 (lg: 1024px+) */}
      <div className="grid md:grid-cols-2 lg:grid-cols-3 gap-4">
        {paths.map((path) => (
          <PathCard key={path.slug} path={path} />
        ))}
      </div>
    </div>
  );
}
