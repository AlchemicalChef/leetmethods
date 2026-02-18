/**
 * @module verifier
 *
 * Client-side Coq proof verification utilities.
 *
 * This module provides two key verification checks that run BEFORE and AFTER
 * executing code through jsCoq:
 *
 * 1. **Forbidden Tactic Detection** (`checkForbiddenTactics`): A pre-execution
 *    check that scans user code for disallowed tactics like `admit` and
 *    `Admitted`. This prevents users from "solving" problems by just admitting
 *    the proof. The check is string-based and comment-aware -- tactics inside
 *    `(* comments *)` are correctly ignored.
 *
 * 2. **Proof Completion Detection** (`isProofComplete`): A post-execution check
 *    that verifies the user's code ends with a proof terminator (`Qed` or
 *    `Defined`). Combined with jsCoq's goal state (zero remaining goals),
 *    this confirms a proof is genuinely complete.
 *
 * ## Why Comment Stripping Matters
 *
 * Problem templates typically end with `Admitted.` as a placeholder. If a user
 * writes their proof but leaves a comment containing "Admitted", the checker
 * must not flag it. Similarly, a user might comment out an `admit` tactic
 * while developing their proof. The `stripCoqComments` function handles all
 * these cases by removing comments before pattern matching.
 *
 * ## Relationship to CoqService.verify()
 *
 * `CoqService.verify()` calls `checkForbiddenTactics()` as its first step
 * (fast client-side rejection) and `isProofComplete()` after execution to
 * determine the final verification result. These functions do NOT execute
 * any Coq code -- they are purely string-based checks.
 *
 * @see CoqService.ts - The verify() method that orchestrates these checks
 * @see coq-parser.ts - Uses a similar comment-stripping approach
 */

/* ==============================================================================
 * Forbidden Tactic Patterns
 * ==============================================================================
 * Pre-compiled regex patterns for commonly forbidden tactics. Using word
 * boundaries (\b) ensures we match whole words only -- `admit` won't match
 * inside `admitted_lemma` or `readmit`.
 *
 * These are the "known" patterns with optimized regexes. Unknown tactic names
 * (passed at runtime) get dynamically compiled with proper escaping.
 * =========================================================================== */

/**
 * Map of known forbidden tactic names to their pre-compiled regex patterns.
 * Each pattern uses `\b` word boundaries to prevent false positives from
 * substrings (e.g., `admit` should not match inside `admitted_count`).
 */
const FORBIDDEN_TACTICS_PATTERNS: Record<string, RegExp> = {
  admit: /\badmit\b/,
  Admitted: /\bAdmitted\b/,
  Abort: /\bAbort\b/,
  Axiom: /\bAxiom\b/,
  Parameter: /\bParameter\b/,
  Conjecture: /\bConjecture\b/,
};

import { stripCoqComments } from './coq-comment';

/* ==============================================================================
 * Forbidden Tactic Checker
 * =========================================================================== */

/**
 * Checks whether user code contains any forbidden tactics.
 *
 * This is the first validation step in `CoqService.verify()`. If forbidden
 * tactics are found, verification is immediately rejected without running
 * the code through jsCoq, providing instant feedback.
 *
 * The check:
 * 1. Strips all comments from the code (to avoid false positives)
 * 2. Tests each forbidden tactic against the stripped code using word-boundary regexes
 * 3. Returns both a boolean flag and the list of found tactics
 *
 * For known tactic names, a pre-compiled regex is used for performance.
 * For unknown names, a regex is dynamically created with proper escaping
 * to handle any special characters in the tactic name.
 *
 * @param code - The user's Coq source code to check
 * @param forbiddenTactics - Array of tactic names that are not allowed
 * @returns Object with `hasForbidden` boolean and `found` array of matched tactic names
 *
 * @example
 * ```ts
 * checkForbiddenTactics("intros. admit.", ["admit", "Admitted"])
 * // Returns: { hasForbidden: true, found: ["admit"] }
 *
 * checkForbiddenTactics("(* admit *) intros. exact H.", ["admit"])
 * // Returns: { hasForbidden: false, found: [] }  // "admit" is inside a comment
 * ```
 */
export function checkForbiddenTactics(
  code: string,
  forbiddenTactics: string[]
): { hasForbidden: boolean; found: string[] } {
  const found: string[] = [];
  const stripped = stripCoqComments(code);

  for (const tactic of forbiddenTactics) {
    // Use the pre-compiled pattern if available; otherwise dynamically create
    // a word-boundary regex with special characters properly escaped
    const pattern = FORBIDDEN_TACTICS_PATTERNS[tactic]
      ?? new RegExp(`\\b${tactic.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\b`);
    if (pattern.test(stripped)) {
      found.push(tactic);
    }
  }

  return {
    hasForbidden: found.length > 0,
    found,
  };
}

/* ==============================================================================
 * Proof Completion Checker
 * =========================================================================== */

/**
 * Checks whether the user's code ends with a proof terminator (`Qed` or `Defined`).
 *
 * In Coq, a proof is not considered complete until it is sealed with `Qed`
 * (makes the proof opaque) or `Defined` (makes the proof transparent/computable).
 * Simply having zero remaining goals is not enough -- the terminator is required.
 *
 * The check strips comments before testing to avoid matching `Qed` inside
 * a comment. The pattern requires `Qed.` or `Defined.` followed by optional
 * whitespace at the end of a line (using the `m` multiline flag).
 *
 * This function is used by `CoqService.verify()` alongside the goal count
 * to determine final proof status:
 * - `isComplete = goals.length === 0 && isProofComplete(code) && errors.length === 0`
 *
 * @param code - The user's Coq source code
 * @returns True if the code ends with `Qed.` or `Defined.`
 */
export function isProofComplete(code: string): boolean {
  // Strip comments first to avoid matching Qed/Defined inside comments
  const stripped = stripCoqComments(code);
  // Match Qed or Defined as a whole word, followed by a period and optional
  // trailing whitespace at the end of a line
  const terminatorPattern = /\b(?:Qed|Defined)\s*\.\s*$/m;
  return terminatorPattern.test(stripped.trim());
}
