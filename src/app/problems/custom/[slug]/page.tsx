/**
 * @module CustomProblemPage
 *
 * Client-rendered page for the `/problems/custom/[slug]` dynamic route.
 *
 * This page renders the interactive Coq proof editor for a user-created
 * custom problem. Custom problems live in the Zustand `customProblemStore`
 * (persisted in localStorage), separate from the built-in problem registry.
 *
 * Key design decisions:
 *
 * 1. **Hydration guard**: Because custom problems are stored in localStorage
 *    (via Zustand persist middleware), they are not available during SSR.
 *    The `hydrated` state flag ensures we show a loading spinner until the
 *    client-side store has rehydrated from localStorage. Without this guard,
 *    the page would briefly flash a "not found" message on every load.
 *
 * 2. **Soft "not found" handling**: Unlike built-in problems which use
 *    `notFound()` to trigger the 404 boundary, custom problems show an
 *    inline error message with a "Back to Problems" button. This is
 *    friendlier since the problem may have been intentionally deleted by
 *    the user, and the URL might have been shared or bookmarked.
 *
 * 3. **Problem summaries for navigation**: Built-in problem summaries are
 *    loaded via `getAllProblems()` and stripped down to `ProblemSummary`
 *    shape, then passed to `ProblemSolver` for its navigation sidebar.
 *    This lets users navigate between custom and built-in problems from
 *    the same interface.
 *
 * 4. **Shared ProblemSolver**: The same `ProblemSolver` component is used
 *    for both built-in and custom problems, ensuring a consistent solving
 *    experience (same editor, goals panel, verification flow).
 */
'use client';

import { useEffect, useState } from 'react';
import { useParams, useRouter } from 'next/navigation';
import { useCustomProblemStore } from '@/store/customProblemStore';
import { ProblemSolver } from '@/components/problem/ProblemSolver';
import { getAllProblems } from '@/lib/problems/loader';
import type { ProblemSummary } from '@/lib/problems/types';

/**
 * Page component for solving a user-created custom problem.
 *
 * Waits for Zustand store hydration before attempting to load the problem,
 * then renders the `ProblemSolver` with the custom problem definition.
 *
 * @returns A loading spinner during hydration, a "not found" message if the
 *   slug is invalid, or the ProblemSolver for the custom problem.
 */
export default function CustomProblemPage() {
  const params = useParams();
  const router = useRouter();
  const slug = params.slug as string;
  const getProblem = useCustomProblemStore((s) => s.getProblem);

  /**
   * Hydration flag: starts as `false` during SSR / initial render, flips
   * to `true` after the first client-side effect. This ensures the
   * localStorage-backed store has populated before we attempt to read from it.
   */
  const [hydrated, setHydrated] = useState(false);

  useEffect(() => {
    setHydrated(true);
  }, []);

  /* ---------------------------------------------------------------- */
  /*  Pre-hydration loading spinner                                    */
  /* ---------------------------------------------------------------- */

  if (!hydrated) {
    return (
      <div className="flex items-center justify-center h-[calc(100vh-64px)]">
        <div className="animate-spin rounded-full h-8 w-8 border-2 border-primary border-t-transparent" />
      </div>
    );
  }

  /* ---------------------------------------------------------------- */
  /*  Problem lookup (post-hydration)                                  */
  /* ---------------------------------------------------------------- */

  const problem = getProblem(slug);

  if (!problem) {
    return (
      <div className="max-w-4xl mx-auto px-4 py-16 text-center">
        <h1 className="text-2xl font-bold mb-4">Custom Problem Not Found</h1>
        <p className="text-muted-foreground mb-6">
          This custom problem may have been deleted or the URL is incorrect.
        </p>
        <button onClick={() => router.push('/problems')} className="text-primary hover:underline">
          Back to Problems
        </button>
      </div>
    );
  }

  /* ---------------------------------------------------------------- */
  /*  Build navigation summaries and render solver                     */
  /* ---------------------------------------------------------------- */

  /**
   * Convert full built-in problem definitions to lightweight summaries
   * for the ProblemSolver's navigation sidebar. We destructure only the
   * fields that `ProblemSummary` requires to avoid passing unnecessary
   * data (templates, solutions, etc.) into the client component tree.
   */
  const builtinSummaries: ProblemSummary[] = getAllProblems().map(
    ({ id, slug, title, difficulty, category, tags }) => ({ id, slug, title, difficulty, category, tags })
  );

  return <ProblemSolver problem={problem} allProblems={builtinSummaries} />;
}
