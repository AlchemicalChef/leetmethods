/**
 * @module TutorialDynamicPage
 *
 * Client-rendered page for the `/tutorial/[slug]` dynamic route.
 *
 * This is the single dynamic route that serves ALL tutorials in the
 * application. Rather than having a separate route file for each tutorial,
 * the tutorial system uses a registry pattern:
 *
 *   1. All tutorial definitions are registered in `src/lib/tutorial/registry.ts`
 *      with a unique `slug`, `title`, `storageKey`, `steps`, and
 *      `completionLink`.
 *   2. This dynamic page extracts the `slug` from the URL, looks up the
 *      matching `TutorialConfig` from the registry, and passes its data
 *      to the generic `TutorialPage` component.
 *   3. If no tutorial matches the slug, `notFound()` triggers the nearest
 *      404 boundary.
 *
 * This approach has several advantages:
 * - Adding a new tutorial requires only adding its step definitions and
 *   registering it in the registry -- no new route files needed.
 * - The `TutorialPage` component handles all interactive tutorial logic
 *   (step navigation, Coq editor integration, progress persistence)
 *   uniformly for all tutorials.
 * - Each tutorial gets its own `storageKey` for independent progress
 *   tracking in localStorage.
 *
 * Why this is a client component:
 * - `useParams()` requires client-side rendering to extract the dynamic
 *   route segment.
 * - The `TutorialPage` component it renders is highly interactive (Coq
 *   editor, goals panel, step navigation).
 */
'use client';

import { useParams } from 'next/navigation';
import { notFound } from 'next/navigation';
import { TutorialPage } from '@/components/tutorial/TutorialPage';
import { getTutorialBySlug } from '@/lib/tutorial/registry';

/**
 * Dynamic tutorial page component.
 *
 * Extracts the tutorial slug from the URL, resolves the corresponding
 * tutorial configuration from the registry, and renders the generic
 * `TutorialPage` component with that configuration.
 *
 * @returns The TutorialPage component configured for the requested tutorial,
 *   or triggers a 404 if the slug is not found in the registry.
 */
export default function TutorialDynamicPage() {
  /**
   * Extract the `slug` param with a type hint. `useParams` returns
   * `string | string[]` by default, but the generic overload narrows
   * it to `string` for single-segment dynamic routes.
   */
  const { slug } = useParams<{ slug: string }>();

  /**
   * Look up the tutorial configuration by slug. Returns `undefined` if
   * no tutorial with this slug is registered.
   */
  const config = getTutorialBySlug(slug);
  if (!config) notFound();

  return (
    <TutorialPage
      steps={config.steps}
      title={config.title}
      storageKey={config.storageKey}
      completionLink={config.completionLink}
    />
  );
}
