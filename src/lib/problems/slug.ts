/**
 * Slug generation utility for custom problems.
 *
 * When users create custom Coq problems via the problem creation form, each
 * problem needs a unique, URL-safe slug for routing and storage. This module
 * generates slugs from problem titles with the following guarantees:
 *
 * - All slugs are prefixed with 'custom-' to distinguish them from built-in
 *   problems and prevent slug collisions with the main problem registry.
 * - Slugs are lowercased, with non-alphanumeric characters replaced by hyphens.
 * - Leading and trailing hyphens are stripped.
 * - Slugs are capped at 50 characters (before the 'custom-' prefix) to prevent
 *   excessively long URLs.
 * - If a collision occurs with an existing slug, a numeric suffix is appended
 *   (e.g., 'custom-my-problem-2', 'custom-my-problem-3').
 *
 * @module problems/slug
 */

/**
 * Generates a unique, URL-safe slug for a custom problem based on its title.
 *
 * The slug is derived by:
 * 1. Lowercasing the title.
 * 2. Replacing runs of non-alphanumeric characters with hyphens.
 * 3. Stripping leading/trailing hyphens.
 * 4. Truncating to 50 characters.
 * 5. Prepending 'custom-' (or 'custom-untitled' if the title produces an empty string).
 * 6. Appending a numeric suffix if the slug already exists in `existingSlugs`.
 *
 * @param title - The user-provided problem title.
 * @param existingSlugs - Array of slugs that are already in use (both built-in
 *                        and custom). The generated slug is guaranteed not to
 *                        collide with any of these.
 * @returns A unique slug string prefixed with 'custom-'.
 *
 * @example
 * ```ts
 * generateSlug('My First Proof', []);
 * // => 'custom-my-first-proof'
 *
 * generateSlug('My First Proof', ['custom-my-first-proof']);
 * // => 'custom-my-first-proof-2'
 *
 * generateSlug('', []);
 * // => 'custom-untitled'
 * ```
 */
export function generateSlug(title: string, existingSlugs: string[]): string {
  const stripped = title
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, '-')
    .replace(/(^-|-$)/g, '')
    .slice(0, 50);
  const base = 'custom-' + (stripped || 'untitled');

  /* If the base slug is not taken, use it directly */
  if (!existingSlugs.includes(base)) return base;

  /* Otherwise, find the lowest available numeric suffix starting from 2 */
  let suffix = 2;
  while (existingSlugs.includes(`${base}-${suffix}`)) {
    suffix++;
  }
  return `${base}-${suffix}`;
}
