/**
 * @module useHydrated
 *
 * Utility hook for detecting when client-side hydration is complete in
 * a Next.js App Router application.
 *
 * In Next.js with SSR/SSG, the initial render on the server produces HTML
 * that must match the first client render (the "hydration" phase). During
 * hydration, data from client-only sources (like localStorage, which backs
 * all Zustand persisted stores in LeetMethods) is not yet available. This
 * creates a mismatch: the server renders default/empty state, but the
 * client would render the persisted state, causing a hydration error.
 *
 * This hook solves the problem by returning `false` during SSR and the
 * first client render (hydration), then `true` on all subsequent renders.
 * Components that depend on persisted state can conditionally render:
 *
 * ```tsx
 * const hydrated = useHydrated();
 * if (!hydrated) return <Skeleton />;
 * // Safe to read from Zustand persisted stores here
 * ```
 *
 * How it works:
 * - `useState(false)` ensures the initial render (which must match SSR)
 *   returns `false`.
 * - `useEffect` runs only on the client, after the initial render/hydration.
 *   It sets the state to `true`, triggering a second render where the
 *   component can safely access client-only data.
 * - The empty dependency array `[]` ensures this runs exactly once.
 *
 * This is a standard Next.js pattern sometimes called "useIsClient" or
 * "useMounted". It is intentionally minimal -- a single boolean state flip.
 */

import { useState, useEffect } from 'react';

/**
 * Returns `true` after the first client-side render (hydration complete),
 * `false` during SSR and the hydration render.
 *
 * Use this to gate rendering of components that depend on client-only data
 * (localStorage, window properties, Zustand persisted stores) to avoid
 * SSR hydration mismatches.
 *
 * @returns `false` on SSR and during hydration, `true` on all subsequent client renders.
 */
export function useHydrated(): boolean {
  const [hydrated, setHydrated] = useState(false);
  useEffect(() => {
    setHydrated(true);
  }, []);
  return hydrated;
}
