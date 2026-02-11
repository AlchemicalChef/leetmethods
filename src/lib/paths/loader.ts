/**
 * Learning path loader for the LeetMethods path system.
 *
 * Provides accessor functions to retrieve learning paths by slug or as a
 * complete list. Learning paths are defined statically in `./paths.ts` and
 * loaded synchronously (no async/filesystem operations), matching the pattern
 * used by the problem loader.
 *
 * The loader acts as the public API for path data access, abstracting the
 * underlying data source. If learning paths were ever moved to an external
 * source (e.g., a CMS or API), only this module would need to change.
 *
 * @module paths/loader
 */

import { learningPaths } from './paths';
import type { LearningPath } from './types';

/**
 * Returns the complete list of all learning paths.
 *
 * The returned array is the same reference as the internal `learningPaths`
 * constant, so callers should treat it as read-only.
 *
 * @returns All defined learning paths, in their canonical display order.
 */
export function getAllPaths(): LearningPath[] {
  return learningPaths;
}

/**
 * Finds a single learning path by its URL slug.
 *
 * @param slug - The path's unique slug identifier (e.g., 'boolean-basics').
 * @returns The matching `LearningPath`, or `null` if no path has the given slug.
 */
export function getPathBySlug(slug: string): LearningPath | null {
  return learningPaths.find((p) => p.slug === slug) ?? null;
}
