/**
 * UI constants for consistent styling and ordering across LeetMethods.
 *
 * Centralizes the mapping of domain values (difficulty levels, categories) to
 * their visual representations (colors, labels, sort order). By keeping these
 * in a single module, the application maintains visual consistency and makes
 * it easy to add new categories or adjust styling without hunting through
 * scattered component files.
 *
 * These constants are used by:
 * - Problem list page (badges, filters, sorting)
 * - Learning paths page (difficulty badges)
 * - Stats page (category breakdowns)
 * - Recommendation engine (difficulty ordering)
 *
 * All color strings use Tailwind CSS utility classes with dark mode variants.
 *
 * @module ui-constants
 */

import type { Difficulty, Category } from '@/lib/problems/types';

/* ============================================================================
 * Difficulty Constants
 * ========================================================================= */

/**
 * Tailwind CSS class strings for difficulty level badges.
 *
 * Each difficulty maps to background and text color classes with dark mode
 * support. Used on problem cards and the problem detail page.
 */
export const DIFFICULTY_COLORS: Record<Difficulty, string> = {
  easy: 'bg-green-100 text-green-800 dark:bg-green-900 dark:text-green-200',
  medium: 'bg-yellow-100 text-yellow-800 dark:bg-yellow-900 dark:text-yellow-200',
  hard: 'bg-red-100 text-red-800 dark:bg-red-900 dark:text-red-200',
};

/**
 * Tailwind CSS class strings for learning path difficulty badges.
 *
 * Separate from `DIFFICULTY_COLORS` because paths use different difficulty
 * labels ('beginner', 'intermediate', 'advanced') than problems ('easy',
 * 'medium', 'hard'), though the color scheme is intentionally the same
 * (green -> yellow -> red) for visual consistency.
 */
export const PATH_DIFFICULTY_COLORS: Record<string, string> = {
  beginner: 'bg-green-100 text-green-800 dark:bg-green-900 dark:text-green-200',
  intermediate: 'bg-yellow-100 text-yellow-800 dark:bg-yellow-900 dark:text-yellow-200',
  advanced: 'bg-red-100 text-red-800 dark:bg-red-900 dark:text-red-200',
};

/**
 * Numeric ordering for difficulty levels, used for sorting and comparison.
 *
 * Lower values indicate easier problems. The recommendation engine uses this
 * to suggest the "next harder" difficulty and to sort fallback recommendations
 * from easiest to hardest.
 */
export const DIFFICULTY_ORDER: Record<Difficulty, number> = { easy: 0, medium: 1, hard: 2 };

/* ============================================================================
 * Category Constants
 * ========================================================================= */

/**
 * Human-readable display labels for each problem category.
 *
 * Used in filter dropdowns, category badges, and the stats breakdown table.
 */
export const CATEGORY_LABELS: Record<Category, string> = {
  logic: 'Logic',
  induction: 'Induction',
  lists: 'Lists',
  arithmetic: 'Arithmetic',
  'data-structures': 'Data Structures',
  relations: 'Relations',
  booleans: 'Booleans',
};

/**
 * Tailwind CSS background color classes for category indicators.
 *
 * Used as small colored dots or bars next to category names in the UI
 * to provide quick visual identification. These are solid background
 * colors (no text color) because they are typically used on small
 * decorative elements, not text badges.
 */
export const CATEGORY_COLORS: Record<Category, string> = {
  logic: 'bg-blue-500',
  induction: 'bg-purple-500',
  lists: 'bg-emerald-500',
  arithmetic: 'bg-orange-500',
  'data-structures': 'bg-pink-500',
  relations: 'bg-cyan-500',
  booleans: 'bg-amber-500',
};

/**
 * Canonical display order for categories.
 *
 * Determines the order in which categories appear in filter dropdowns,
 * stats breakdowns, and any other ordered category listing. The order
 * is pedagogical: logic and booleans (foundational) come first, followed
 * by induction, lists, arithmetic, data structures, and relations
 * (progressively more complex topics).
 */
export const CATEGORY_ORDER: Category[] = [
  'logic',
  'booleans',
  'induction',
  'lists',
  'arithmetic',
  'data-structures',
  'relations',
];
