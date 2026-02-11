/**
 * General-purpose utility functions for LeetMethods.
 *
 * Currently provides the `cn()` helper for merging Tailwind CSS class names.
 * This is the standard shadcn/ui utility pattern that combines `clsx` (for
 * conditional class joining) with `tailwind-merge` (for resolving conflicting
 * Tailwind utility classes).
 *
 * Example of why `tailwind-merge` is needed: `cn('px-4', 'px-2')` returns
 * `'px-2'` (the latter wins), whereas plain string concatenation would
 * produce `'px-4 px-2'` where the browser applies whichever class appears
 * last in the stylesheet (unpredictable with Tailwind's generated order).
 *
 * @module utils
 */

import { clsx, type ClassValue } from "clsx"
import { twMerge } from "tailwind-merge"

/**
 * Merges Tailwind CSS class names with conflict resolution.
 *
 * Combines the functionality of `clsx` (conditional class joining with
 * support for strings, objects, and arrays) and `tailwind-merge` (intelligent
 * deduplication of conflicting Tailwind utility classes).
 *
 * @param inputs - Any number of class values: strings, objects with boolean
 *                 values (`{ 'bg-red-500': isError }`), arrays, `undefined`,
 *                 `null`, or `false` (falsy values are filtered out).
 * @returns A single string of merged, deduplicated CSS class names.
 *
 * @example
 * ```ts
 * cn('px-4 py-2', isActive && 'bg-blue-500', 'px-2')
 * // => 'py-2 bg-blue-500 px-2' (px-4 is overridden by px-2)
 * ```
 */
export function cn(...inputs: ClassValue[]) {
  return twMerge(clsx(inputs))
}
