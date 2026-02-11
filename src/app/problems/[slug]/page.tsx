/**
 * @module ProblemPage
 *
 * Server-rendered page for the `/problems/[slug]` dynamic route.
 *
 * This is the main problem-solving page where users write Coq proofs in
 * the browser-based editor. Each built-in problem has a unique slug that
 * maps to a JSON definition in `src/content/problems/{category}/`.
 *
 * Key architecture decisions:
 *
 * 1. **Static generation via `generateStaticParams`**: At build time,
 *    Next.js calls `generateStaticParams()` to enumerate all valid problem
 *    slugs. This allows the pages to be statically generated (SSG) for
 *    fast initial loads. The problem data comes from the synchronous
 *    `getAllProblems()` loader.
 *
 * 2. **Dynamic metadata via `generateMetadata`**: Each problem page gets
 *    a unique `<title>` and `<meta description>` based on the problem's
 *    title, difficulty, and category. This improves SEO and provides
 *    meaningful browser tab titles.
 *
 * 3. **Server-to-client data passing**: The page is an async server
 *    component that resolves the `params` promise (Next.js 15 convention
 *    for dynamic route params), looks up the full problem definition, and
 *    passes it as a prop to the `ProblemSolver` client component. The
 *    `ProblemSolver` handles the interactive Coq editor, goals panel,
 *    and proof verification via the jsCoq iframe.
 *
 * 4. **404 handling**: If the slug does not match any registered problem,
 *    the page calls `notFound()` which triggers the nearest `not-found.tsx`
 *    boundary.
 *
 * 5. **Problem summaries for navigation**: `getProblemSummaries()` is also
 *    loaded and passed to `ProblemSolver` so it can render a problem
 *    navigation sidebar or "next problem" links without needing to load
 *    full problem definitions for every problem.
 */

import { notFound } from 'next/navigation';
import { ProblemSolver } from '@/components/problem/ProblemSolver';
import { getAllProblems, getProblemSummaries } from '@/lib/problems/loader';
import type { Metadata } from 'next';

/* ------------------------------------------------------------------ */
/*  Types                                                              */
/* ------------------------------------------------------------------ */

/**
 * Props for the ProblemPage component and `generateMetadata`.
 * In Next.js 15+, dynamic route params are delivered as a Promise.
 */
interface Props {
  params: Promise<{ slug: string }>;
}

/* ------------------------------------------------------------------ */
/*  Static generation                                                  */
/* ------------------------------------------------------------------ */

/**
 * Enumerates all valid problem slugs at build time so Next.js can
 * statically generate a page for each built-in problem.
 *
 * @returns An array of `{ slug }` objects, one per registered problem.
 */
export function generateStaticParams() {
  const problems = getAllProblems();
  return problems.map((problem) => ({
    slug: problem.slug,
  }));
}

/* ------------------------------------------------------------------ */
/*  Dynamic metadata                                                   */
/* ------------------------------------------------------------------ */

/**
 * Generates page-specific metadata (title and description) based on the
 * problem's slug. If the slug is invalid, a generic "not found" title is
 * returned.
 *
 * @param props - Contains the route params promise with the problem slug.
 * @returns A `Metadata` object with the problem's title and a descriptive
 *   string including difficulty and category.
 */
export async function generateMetadata({ params }: Props): Promise<Metadata> {
  const { slug } = await params;
  const problems = getAllProblems();
  const problem = problems.find((p) => p.slug === slug);

  if (!problem) {
    return { title: 'Problem Not Found - LeetMethods' };
  }

  return {
    title: `${problem.title} - LeetMethods`,
    description: `Solve "${problem.title}" - a ${problem.difficulty} ${problem.category} proof problem. Practice formal verification in Coq.`,
  };
}

/* ------------------------------------------------------------------ */
/*  Page component                                                     */
/* ------------------------------------------------------------------ */

/**
 * Async server component that resolves the problem slug, loads the full
 * problem definition, and renders the interactive `ProblemSolver`.
 *
 * The `ProblemSolver` client component receives:
 *   - `problem`: The full problem definition (title, template, prelude,
 *     solution, hints, forbidden tactics, etc.).
 *   - `allProblems`: Lightweight summaries of every problem, used for
 *     the problem navigation sidebar and "next problem" links.
 *
 * @param props - Contains the route params promise with the problem slug.
 * @returns The ProblemSolver component, or triggers a 404 if the slug
 *   is not found.
 */
export default async function ProblemPage({ params }: Props) {
  const { slug } = await params;
  const problems = getAllProblems();
  const problem = problems.find((p) => p.slug === slug);

  if (!problem) {
    notFound();
  }

  const allProblems = getProblemSummaries();

  return <ProblemSolver problem={problem} allProblems={allProblems} />;
}
