/**
 * Error formatting utility for catch blocks.
 *
 * In TypeScript, the `catch` clause variable is typed as `unknown`, which means
 * callers must handle the possibility that the caught value is not an `Error` instance.
 * This utility centralizes that logic so that every catch block in the application
 * can produce a consistent, human-readable error message.
 *
 * The priority order is:
 * 1. If the value is an `Error` instance, use its `.message` property.
 * 2. If the value is a raw string (some libraries throw strings), use it directly.
 * 3. Otherwise, fall back to the caller-provided default message.
 *
 * This is used extensively in CoqService, the verifier, and UI components
 * that catch errors from the jsCoq iframe communication layer.
 *
 * @module format-error
 */

/**
 * Extracts a human-readable message from an unknown caught value.
 *
 * @param error - The value caught in a `catch` block (typed as `unknown`).
 * @param fallback - A default message to return if the error is neither an
 *                   `Error` instance nor a string.
 * @returns A string suitable for displaying to the user or logging.
 *
 * @example
 * ```ts
 * try {
 *   await coqService.verify(code);
 * } catch (err) {
 *   setErrorMessage(formatError(err, 'Verification failed'));
 * }
 * ```
 */
export function formatError(error: unknown, fallback: string): string {
  if (error instanceof Error) return error.message;
  if (typeof error === 'string') return error;
  return fallback;
}
