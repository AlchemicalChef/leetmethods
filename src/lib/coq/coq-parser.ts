/**
 * @module coq-parser
 *
 * Context-aware Coq source code parser and goal data transformer.
 *
 * This module provides three critical capabilities:
 *
 * 1. **Statement Splitting** (`parseStatements`): Splits Coq source code into
 *    individual sentences (statements). This is non-trivial because Coq uses `.`
 *    as a sentence terminator, but `.` also appears in qualified names like
 *    `Nat.add`. The parser tracks nested `(* ... *)` comments, `"strings"`,
 *    and requires whitespace or EOF after `.` to recognize a sentence boundary.
 *
 * 2. **Proof Detection** (`isProofStart`): Determines whether a Coq statement
 *    is a `Proof` command, accounting for comments and strings that might
 *    contain the word "Proof" without it being a command.
 *
 * 3. **Goal Parsing** (`parseGoalData`, `ppToString`, `stripPpTags`): Transforms
 *    jsCoq's raw goal data (which uses a "Pp" pretty-printing AST format) into
 *    the typed `CoqGoal[]` array used by the UI.
 *
 * ## Design Decisions
 *
 * - The parser is intentionally imperative (character-by-character iteration)
 *   rather than regex-based, because Coq's nested comment syntax `(* (* ... *) *)`
 *   cannot be correctly handled by regular expressions.
 * - Coq strings use `""` for escaped quotes (not `\"`), which differs from most
 *   languages and must be handled explicitly.
 * - The `Pp` AST format from jsCoq is a nested array structure (e.g.,
 *   `['Pp_glue', [['Pp_string', 'nat'], ...]]`) that must be recursively
 *   flattened to plain text for display.
 *
 * @see CoqService.ts - Primary consumer; uses parseStatements for step-by-step execution
 * @see verifier.ts - Uses a similar comment-stripping approach for forbidden tactic detection
 */
import type { CoqGoal } from './types';

/* ==============================================================================
 * Pp (Pretty-Print) AST Conversion
 * ==============================================================================
 * jsCoq represents formatted text using a "Pp" AST — a recursive structure of
 * tagged arrays. These functions convert that AST to plain text strings for
 * display in the goals panel and other UI elements.
 *
 * The Pp AST node types:
 * - Pp_string: Leaf node containing literal text
 * - Pp_glue: Concatenation of child nodes
 * - Pp_box: Box layout container (children concatenated)
 * - Pp_tag: Semantic tag wrapping a child node (tag is ignored, child is extracted)
 * - Pp_force_newline: Line break (rendered as space)
 * - Pp_print_break: Breakable space (rendered as space)
 * =========================================================================== */

/**
 * Recursively converts a Pp AST (nested arrays from jsCoq) into plain text.
 *
 * The Pp format is how Coq's pretty-printer represents structured output.
 * Each node is an array where the first element is the tag name and
 * subsequent elements are children or content.
 *
 * @param pp - A Pp AST node, which can be a string, array, or other value
 * @returns The flattened plain text representation
 *
 * @example
 * ```ts
 * ppToString(['Pp_glue', [['Pp_string', 'nat'], ['Pp_string', ' -> nat']]])
 * // Returns: "nat -> nat"
 * ```
 */
export function ppToString(pp: unknown): string {
  if (typeof pp === 'string') return pp;
  if (!Array.isArray(pp)) return String(pp);
  const tag = pp[0];
  // Pp_string is a leaf node: ['Pp_string', 'some text']
  if (tag === 'Pp_string') return (pp[1] as string) || '';
  // Pp_glue and Pp_box contain a list of children to concatenate
  if (tag === 'Pp_glue' || tag === 'Pp_box') return ((pp[1] as unknown[]) || []).map(c => ppToString(c)).join('');
  // Pp_tag wraps a child with a semantic tag: ['Pp_tag', 'tag_name', child]
  if (tag === 'Pp_tag') return ppToString(pp[2]);
  // Pp_force_newline and Pp_print_break represent whitespace in the layout
  if (tag === 'Pp_force_newline' || tag === 'Pp_print_break') return ' ';
  // Fallback: concatenate all children (skip the tag name at index 0)
  return pp.slice(1).map((c: unknown) => ppToString(c)).join('');
}

/**
 * Converts a Pp AST or a string with XML-like Pp tags to plain text.
 *
 * jsCoq sometimes returns goal/hypothesis text as strings containing
 * XML-like tags (e.g., `<Pp_tag>text</Pp_tag>`). This function handles
 * both the array AST format and the string-with-tags format.
 *
 * @param s - Either a Pp AST array or a string potentially containing Pp XML tags
 * @returns Clean plain text with all Pp markup removed
 */
export function stripPpTags(s: unknown): string {
  // If it's an array, it's a Pp AST -- delegate to ppToString
  if (Array.isArray(s)) return ppToString(s);
  if (typeof s !== 'string') return String(s);
  // Strip XML-like Pp tags (e.g., <Pp_tag>, </Pp_tag>, <constr.variable>)
  return s.replace(/<\/?Pp_[^>]*>/g, '').replace(/<\/?[a-z_]+>/gi, '').trim();
}

/* ==============================================================================
 * Goal Data Parsing
 * ==============================================================================
 * Transforms the raw goal data from jsCoq's postMessage into typed CoqGoal[].
 * jsCoq hypotheses are 3-element tuples: [names, definition, type]
 * where `definition` is null/undefined for regular (non-let) hypotheses.
 * =========================================================================== */

/**
 * Parses raw jsCoq goal data into a typed `CoqGoal[]` array.
 *
 * jsCoq sends goal data via postMessage with the structure:
 * ```
 * { goals: [{ hyp: [[names, def, type], ...], ty: PpAst }, ...] }
 * ```
 *
 * Each hypothesis is a 3-tuple where:
 * - `h[0]` is the name(s) — may be a string or array of strings
 * - `h[1]` is the definition (for `let` bindings; null for regular hyps)
 * - `h[2]` is the type (as a Pp AST)
 *
 * When `h[2]` is missing (older jsCoq format), `h[1]` is used as the type.
 * The goal conclusion may be in `g.ty` (newer) or `g.ccl` (older).
 *
 * @param goalData - Raw goal data from jsCoq's postMessage event
 * @returns Array of parsed CoqGoal objects with plain-text hypotheses and conclusions
 */
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export function parseGoalData(goalData: any): CoqGoal[] {
  if (!goalData?.goals) return [];

  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  return goalData.goals.map((g: any, index: number) => ({
    id: index + 1,
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    hypotheses: (g.hyp || []).map((h: any) => ({
      // Names can be a single string or array of strings (for grouped hyps like "x y : nat")
      name: (Array.isArray(h[0]) ? h[0] : [h[0]]).join(', '),
      // Type is at index 2 if present (3-tuple format), otherwise index 1 (2-tuple format)
      type: stripPpTags(h[2] ?? h[1]),
    })),
    // Conclusion can be in .ty (standard) or .ccl (older jsCoq versions)
    conclusion: stripPpTags(g.ty ?? g.ccl),
  }));
}

/* ==============================================================================
 * Proof Start Detection
 * ==============================================================================
 * Determines whether a given Coq statement is a `Proof` command. This is used
 * by CoqService to track whether proof mode has been entered, which affects
 * the UI (e.g., showing the goals panel).
 * =========================================================================== */

/**
 * Checks if a Coq statement is a `Proof` command.
 *
 * The check is context-aware: it strips comments and strings before testing,
 * so `(* Proof *)` inside a comment or `"Proof"` inside a string won't
 * produce a false positive.
 *
 * Uses the same depth-counting comment parser as `parseStatements` to ensure
 * consistent behavior. Coq comments nest: `(* (* inner *) outer *)` is valid.
 *
 * @param statement - A single Coq statement (as returned by parseStatements)
 * @returns True if the statement is a `Proof` command
 */
export function isProofStart(statement: string): boolean {
  // Strip nested comments and strings using the same depth-counting approach
  // as parseStatements, ensuring consistent parsing behavior
  let stripped = '';
  let commentDepth = 0;
  let inString = false;

  for (let i = 0; i < statement.length; i++) {
    const char = statement[i];
    const next = statement[i + 1];

    // Enter a nested comment: `(*`
    if (char === '(' && next === '*' && !inString) {
      commentDepth++;
      i++;
      continue;
    }
    // Exit a nested comment: `*)`
    if (char === '*' && next === ')' && commentDepth > 0 && !inString) {
      commentDepth--;
      i++;
      continue;
    }
    // Handle Coq string boundaries and escaped quotes (`""`)
    if (char === '"' && commentDepth === 0) {
      if (inString && next === '"') {
        i++; // Skip escaped quote (`""` inside strings)
        continue;
      }
      inString = !inString;
      continue;
    }
    // Only accumulate characters that are outside comments and strings
    if (commentDepth === 0 && !inString) {
      stripped += char;
    }
  }

  // Match "Proof" at the start of the stripped statement (with optional leading whitespace)
  // The \b word boundary prevents matching "ProofIrrelevance" or similar
  return /^\s*Proof\b/.test(stripped);
}

/* ==============================================================================
 * Statement Parser
 * ==============================================================================
 * The core sentence splitter for Coq source code. Coq sentences are terminated
 * by a period (`.`) followed by whitespace or end-of-file. The period in
 * qualified names like `Nat.add` or `List.map` does NOT terminate a sentence
 * because it is followed by an identifier character, not whitespace.
 *
 * This parser correctly handles:
 * - Nested comments: `(* (* inner *) outer *)`
 * - Strings with escaped quotes: `"hello ""world"""`
 * - Qualified names: `Nat.add`, `Coq.Init.Logic`
 * - Multi-line statements
 * =========================================================================== */

/**
 * Splits Coq source code into individual statements (sentences).
 *
 * Coq's sentence terminator is a period (`.`) followed by whitespace or EOF.
 * This distinguishes sentence-ending periods from those in qualified names
 * like `Nat.add` (where the period is followed by a letter, not whitespace).
 *
 * The parser tracks three kinds of context:
 * 1. **Comment depth** (`commentDepth`): Coq comments nest, so `(* (* *) *)` is
 *    one comment. Periods inside comments are ignored.
 * 2. **String state** (`inString`): Periods inside `"strings"` are ignored.
 *    Coq uses `""` for escaped quotes inside strings (not `\"`).
 * 3. **Normal code**: Only periods in normal code context are candidates for
 *    sentence terminators.
 *
 * @param code - Full Coq source code to parse
 * @returns Array of trimmed Coq statements in order of appearance
 *
 * @example
 * ```ts
 * parseStatements("Require Import Nat. Theorem t : 1 + 1 = 2. Proof. lia. Qed.")
 * // Returns: [
 * //   "Require Import Nat.",
 * //   "Theorem t : 1 + 1 = 2.",
 * //   "Proof.",
 * //   "lia.",
 * //   "Qed."
 * // ]
 * ```
 */
export function parseStatements(code: string): string[] {
  const statements: string[] = [];
  let current = '';
  let commentDepth = 0;
  let inString = false;

  for (let i = 0; i < code.length; i++) {
    const char = code[i];
    const next = code[i + 1];

    // Detect opening of a nested comment: `(*`
    // Comments can nest in Coq, so we track depth rather than a boolean
    if (char === '(' && next === '*' && !inString) {
      commentDepth++;
      current += '(*';
      i++;
      continue;
    }

    // Detect closing of a nested comment: `*)`
    // Only close if we're actually inside a comment (depth > 0)
    if (char === '*' && next === ')' && commentDepth > 0 && !inString) {
      commentDepth--;
      current += '*)';
      i++;
      continue;
    }

    // Handle Coq string literals. Coq uses `""` for escaped quotes inside
    // strings (not backslash like most languages). So `"hello ""world"""` is
    // the string `hello "world"`.
    if (char === '"' && commentDepth === 0) {
      if (inString && next === '"') {
        current += '""';
        i++;
        continue;
      }
      inString = !inString;
    }

    current += char;

    // Check for sentence terminator: period followed by whitespace or EOF.
    // This is the key rule that prevents splitting on qualified names like
    // `Nat.add` -- the period there is followed by 'a', not whitespace.
    if (char === '.' && commentDepth === 0 && !inString) {
      const nextChar = code[i + 1];
      if (nextChar === undefined || /\s/.test(nextChar)) {
        const trimmed = current.trim();
        if (trimmed) {
          statements.push(trimmed);
        }
        current = '';
      }
    }
  }

  return statements;
}
