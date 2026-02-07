/**
 * Extracts a human-readable message from an unknown caught value.
 * Use in catch blocks: `formatError(err, 'Execution failed')`
 */
export function formatError(error: unknown, fallback: string): string {
  if (error instanceof Error) return error.message;
  if (typeof error === 'string') return error;
  return fallback;
}
