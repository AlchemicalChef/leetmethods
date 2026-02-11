/**
 * @module PathDetailPage
 *
 * Client-rendered page for the `/learn/[slug]` dynamic route.
 *
 * This page displays a single Learning Path in detail: its title, difficulty
 * badge, description, an animated progress bar, and an ordered list of
 * steps (problems) that make up the path.
 *
 * Why this is a client component:
 * - It needs to read user progress from the Zustand `progressStore`, which
 *   is persisted in localStorage and only available on the client.
 * - It uses `useParams()` from `next/navigation` to extract the dynamic
 *   `[slug]` segment, which requires client-side rendering.
 *
 * Data flow:
 * 1. The `slug` is extracted from the URL via `useParams()`.
 * 2. `getPathBySlug(slug)` performs a synchronous lookup in the static
 *    path registry to find the path definition.
 * 3. If the path is not found, a fallback "not found" message is shown
 *    with a link back to `/learn` (we do not call `notFound()` here
 *    because this is a client component and we want a softer UX).
 * 4. `computePathProgress()` combines the path definition with the user's
 *    progress record to calculate completed/total step counts and a
 *    percentage for the progress bar.
 * 5. The `PathStepList` component renders each step as a card with
 *    completion status indicators.
 *
 * The `PATH_DIFFICULTY_COLORS` constant maps difficulty levels (beginner,
 * intermediate, advanced) to Tailwind color classes for the difficulty badge.
 */
'use client';

import { useParams } from 'next/navigation';
import Link from 'next/link';
import { Badge } from '@/components/ui/badge';
import { ArrowLeft } from 'lucide-react';
import { getPathBySlug } from '@/lib/paths/loader';
import { PathStepList } from '@/components/learn/PathStepList';
import { useProgressStore } from '@/store/progressStore';
import { computePathProgress } from '@/lib/paths/progress';
import { PATH_DIFFICULTY_COLORS } from '@/lib/ui-constants';

/**
 * Detail page for a single learning path, identified by its URL slug.
 *
 * Displays the path header (icon, title, difficulty badge, description),
 * an animated progress bar showing completion percentage, and the ordered
 * list of path steps.
 *
 * @returns The path detail page, or a "not found" fallback if the slug
 *   does not match any registered path.
 */
export default function PathDetailPage() {
  const params = useParams();

  /**
   * The slug is always a string in this route, but `useParams()` returns
   * `string | string[]` so we cast to `string` for type safety.
   */
  const slug = params.slug as string;
  const path = getPathBySlug(slug);

  /**
   * Subscribe to the full progress record from Zustand. This is an object
   * keyed by problem slug, with each value containing completion status,
   * attempt counts, SRS scheduling data, etc.
   */
  const progress = useProgressStore((s) => s.progress);

  /* ---------------------------------------------------------------- */
  /*  Path not found fallback                                          */
  /* ---------------------------------------------------------------- */

  if (!path) {
    return (
      <div className="max-w-4xl mx-auto px-4 py-12 text-center">
        <h1 className="text-2xl font-bold mb-4">Path not found</h1>
        <Link href="/learn" className="text-primary hover:underline">
          Back to Learn
        </Link>
      </div>
    );
  }

  /* ---------------------------------------------------------------- */
  /*  Compute progress metrics                                         */
  /* ---------------------------------------------------------------- */

  /**
   * Derives `completedSteps`, `totalSteps`, and `percent` by cross-referencing
   * the path's step list with the user's progress record.
   */
  const pathProgress = computePathProgress(path, progress);

  /* ---------------------------------------------------------------- */
  /*  Render                                                           */
  /* ---------------------------------------------------------------- */

  return (
    <div className="max-w-4xl mx-auto px-4 py-12">
      {/* Back navigation link */}
      <Link
        href="/learn"
        className="inline-flex items-center gap-1 text-sm text-muted-foreground hover:text-foreground mb-6"
      >
        <ArrowLeft className="h-4 w-4" />
        Back to Learn
      </Link>

      {/* Path header: icon, title with difficulty badge, and description */}
      <div className="flex items-start gap-4 mb-6">
        <span className="text-4xl">{path.icon}</span>
        <div>
          <div className="flex items-center gap-2 mb-1">
            <h1 className="text-3xl font-bold">{path.title}</h1>
            <Badge className={PATH_DIFFICULTY_COLORS[path.difficulty]}>
              {path.difficulty}
            </Badge>
          </div>
          <p className="text-muted-foreground">{path.description}</p>
        </div>
      </div>

      {/* Animated progress bar showing path completion percentage */}
      <div className="flex items-center gap-3 mb-8">
        <div className="flex-1 h-2 bg-muted rounded-full overflow-hidden">
          <div
            className="h-full bg-primary rounded-full transition-all duration-500"
            style={{ width: `${pathProgress.percent}%` }}
          />
        </div>
        <span className="text-sm font-medium">
          {pathProgress.completedSteps}/{pathProgress.totalSteps} complete
        </span>
      </div>

      {/* Ordered list of path steps with per-step completion indicators */}
      <PathStepList steps={path.steps} />
    </div>
  );
}
