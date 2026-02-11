/**
 * @module error-helper
 *
 * Coq error message translator for beginner-friendly feedback.
 *
 * Coq's native error messages are often cryptic and assume familiarity with
 * type theory terminology. This module translates common Coq errors into
 * friendly, actionable messages that help beginners understand what went
 * wrong and how to fix it.
 *
 * ## How It Works
 *
 * The module maintains an ordered array of `ErrorPattern` entries, each
 * containing:
 * - A regex `pattern` that matches a specific Coq error format
 * - A `friendly` function that generates a human-readable message using
 *   the regex capture groups
 *
 * When `formatCoqError()` is called with a raw error string, it tests each
 * pattern in order and returns the first match. If no pattern matches, it
 * returns `null` for the friendly message, and the raw error is shown as-is.
 *
 * ## Design Decisions
 *
 * - Patterns are tested in order, so more specific patterns should come before
 *   more general ones. For example, "The term X has type Y while expected Z"
 *   (specific) comes before "In environment... The term" (general).
 * - The friendly messages use second-person language ("Check that your...")
 *   to be approachable and instructive.
 * - Capture groups extract specific details (variable names, types) from the
 *   error to provide context-specific advice.
 * - The `raw` field is always preserved in the result so advanced users can
 *   still see the original Coq error if needed.
 *
 * @see ProblemSolver component - Displays formatted errors to users
 * @see CoqService.ts - Source of raw error messages from jsCoq
 */

/* ==============================================================================
 * Error Pattern Definitions
 * ==============================================================================
 * Each pattern matches a specific Coq error message format. The `friendly`
 * function receives the regex match array and produces a beginner-friendly
 * explanation. Patterns are tested in order -- first match wins.
 * =========================================================================== */

/**
 * Defines a mapping from a Coq error regex to a friendly message generator.
 */
interface ErrorPattern {
  /** Regex to match against the raw Coq error string */
  pattern: RegExp;

  /**
   * Generates a friendly error message from the regex match.
   * @param match - The RegExp match array (m[0] is full match, m[1]+ are capture groups)
   * @returns A human-readable error explanation
   */
  friendly: (match: RegExpMatchArray) => string;
}

/**
 * Ordered list of error patterns. The first matching pattern is used.
 *
 * Categories of errors handled:
 * - **Type mismatches**: Unification failures, wrong types
 * - **Proof state errors**: No more subgoals, no such goal
 * - **Name resolution**: Unknown variables, undefined references
 * - **Tactic failures**: Tactic doesn't apply, missing cases
 * - **Syntax errors**: Malformed Coq code
 * - **Environment errors**: Missing libraries
 */
const errorPatterns: ErrorPattern[] = [
  {
    // Coq's unification failure: two types could not be made equal.
    // This is the most common error beginners encounter -- it means a tactic
    // or expression has the wrong type for the current goal.
    pattern: /Unable to unify "(.+)" with "(.+)"/,
    friendly: (m) => `Type mismatch: expected "${m[2]}" but got "${m[1]}". Check that your expression has the right type.`,
  },
  {
    // All subgoals have been solved, but there's still code after Qed.
    // Common when users add extra tactics after the proof is done.
    pattern: /No more subgoals/,
    friendly: () => `The proof is already complete! Remove extra tactics after Qed.`,
  },
  {
    // The expression being used isn't a valid proposition.
    // Happens when users try to prove something that isn't a Prop.
    pattern: /Not a proposition or a type/,
    friendly: () => `This expression isn't a proposition. Make sure you're proving a logical statement.`,
  },
  {
    // A variable name was used but not introduced into the proof context.
    // Most commonly happens when `intros` hasn't been called yet, or when
    // a hypothesis name is misspelled.
    pattern: /The variable (.+) was not found/,
    friendly: (m) => `Unknown variable "${m[1]}". Did you forget to introduce it with "intros"?`,
  },
  {
    // Coq's typeclass/instance resolution failed.
    // Happens with overloaded operations or when a required instance isn't imported.
    pattern: /Unable to find an instance/,
    friendly: () => `Coq can't automatically find a matching value. Try providing it explicitly.`,
  },
  {
    // A more detailed version of the unification error that names the specific
    // term, its actual type, and the expected type. Provides richer context.
    pattern: /The term "(.+)" has type "(.+)" while it is expected to have type "(.+)"/,
    friendly: (m) => `Wrong type: "${m[1]}" is a "${m[2]}" but needs to be a "${m[3]}".`,
  },
  {
    // A generic type error with environment context. This is a catch-all for
    // type errors that don't match the more specific patterns above.
    pattern: /In environment[\s\S]*?The term/,
    friendly: () => `Type error in the current proof context. Check that your tactic arguments match the goal.`,
  },
  {
    // Trying to operate on a goal that doesn't exist.
    // Happens when the user has already solved all subgoals or is targeting
    // a non-existent goal number.
    pattern: /No such goal/,
    friendly: () => `There's no goal to prove. You may have already completed this part.`,
  },
  {
    // General syntax error. Could be a missing period, unmatched parenthesis,
    // or any other syntactic issue.
    pattern: /Syntax error/,
    friendly: () => `Syntax error in your Coq code. Check for missing periods, parentheses, or typos.`,
  },
  {
    // A name (lemma, theorem, tactic, etc.) was referenced but doesn't exist.
    // Could be a typo or a missing `Require Import` statement.
    pattern: /The reference (.+) was not found/,
    friendly: (m) => `"${m[1]}" is not defined. Check the spelling or make sure the required library is imported.`,
  },
  {
    // A `match` expression doesn't cover all cases of the inductive type.
    // Coq requires exhaustive pattern matching.
    pattern: /No matching clauses for match/,
    friendly: () => `Pattern match is incomplete. Make sure you handle all cases.`,
  },
  {
    // A `Require Import` couldn't find the specified library file.
    // In the jsCoq context, this usually means the library isn't bundled.
    pattern: /Cannot find a physical path/,
    friendly: () => `A required library could not be found. This may be a configuration issue.`,
  },
  {
    // Generic tactic failure. The tactic was syntactically correct but couldn't
    // make progress on the current goal.
    pattern: /Tactic failure/,
    friendly: () => `The tactic failed. The current goal may not match what the tactic expects.`,
  },
];

/* ==============================================================================
 * Error Formatting
 * =========================================================================== */

/**
 * Represents a Coq error with both the raw message and an optional
 * beginner-friendly translation.
 */
export interface FormattedError {
  /** The original error message from Coq */
  raw: string;

  /**
   * A beginner-friendly explanation of the error, or null if no pattern
   * matched (in which case the raw message should be displayed instead)
   */
  friendly: string | null;
}

/**
 * Translates a raw Coq error message into a beginner-friendly format.
 *
 * Tests the raw error against all known patterns in order and returns
 * the first match. If no pattern matches, returns `null` for the friendly
 * field, indicating the raw error should be shown as-is.
 *
 * @param rawError - The raw error string from jsCoq/Coq
 * @returns A FormattedError with the raw message and optional friendly translation
 *
 * @example
 * ```ts
 * formatCoqError('The variable x was not found in the current environment')
 * // Returns: {
 * //   raw: 'The variable x was not found in the current environment',
 * //   friendly: 'Unknown variable "x". Did you forget to introduce it with "intros"?'
 * // }
 *
 * formatCoqError('Some unknown error')
 * // Returns: { raw: 'Some unknown error', friendly: null }
 * ```
 */
export function formatCoqError(rawError: string): FormattedError {
  for (const { pattern, friendly } of errorPatterns) {
    const match = rawError.match(pattern);
    if (match) {
      return { raw: rawError, friendly: friendly(match) };
    }
  }
  return { raw: rawError, friendly: null };
}
