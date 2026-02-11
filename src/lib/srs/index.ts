/**
 * Public API barrel file for the spaced repetition system (SRS).
 *
 * Re-exports the core SM-2 algorithm functions and types from `./algorithm.ts`.
 * The review queue management (`./reviews.ts`) is imported directly by consumers
 * that need it, since it is a higher-level module with additional dependencies.
 *
 * This barrel file allows the rest of the application to import SRS primitives
 * from `@/lib/srs` without knowing the internal file structure:
 *
 * ```ts
 * import { createInitialSrs, calculateNextReview } from '@/lib/srs';
 * import type { SrsData } from '@/lib/srs';
 * ```
 *
 * @module srs
 */

export { createInitialSrs, createMigratedSrs, calculateNextReview, deriveQuality, isReviewDue, daysOverdue } from './algorithm';
export type { SrsData } from './algorithm';
