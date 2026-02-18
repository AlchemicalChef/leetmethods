/**
 * @module coq-comment
 *
 * Shared utilities for Coq nested comment and string scanning.
 *
 * Coq comments nest: `(* (* inner *) outer *)` is valid. Coq strings
 * use `""` for escaped quotes (not `\"`). These utilities centralize
 * the depth-tracking finite-state machine used across the codebase.
 *
 * @see coq-parser.ts - Statement parser (has its own inline scanner that accumulates text)
 * @see verifier.ts - Uses stripCoqComments for forbidden tactic detection
 * @see coq-linter.ts - Uses isInsideCoqComment for static lint warnings
 * @see coq-diagnostics.ts - Uses skipCoqComment for statement position finding
 * @see coq-signature.ts - Uses isInsideCoqComment for signature help
 */

/**
 * Strips all Coq comments from source code, preserving strings.
 *
 * Handles nested `(* ... *)` comments and `""` escaped quotes within strings.
 *
 * @param code - Raw Coq source code
 * @returns The code with all comments removed, strings preserved
 */
export function stripCoqComments(code: string): string {
  let result = '';
  let depth = 0;
  let inString = false;
  for (let i = 0; i < code.length; i++) {
    const char = code[i];
    const next = code[i + 1];

    if (char === '(' && next === '*' && !inString) {
      depth++;
      i++;
      continue;
    }
    if (char === '*' && next === ')' && depth > 0 && !inString) {
      depth--;
      i++;
      continue;
    }
    if (char === '"' && depth === 0) {
      if (inString && next === '"') {
        result += '""';
        i++;
        continue;
      }
      inString = !inString;
    }
    if (depth === 0) {
      result += char;
    }
  }
  return result;
}

/**
 * Checks whether a position in a string is inside a `(* ... *)` comment.
 *
 * Scans from the beginning of `text` up to (but not including) `pos`,
 * tracking comment and string state.
 *
 * @param text - The text to scan
 * @param pos - Character position to check (0-based, exclusive)
 * @returns True if `pos` is inside a Coq comment
 */
export function isInsideCoqComment(text: string, pos: number): boolean {
  let depth = 0;
  let inString = false;
  const limit = Math.min(pos, text.length);
  for (let i = 0; i < limit; i++) {
    const ch = text[i];
    const next = text[i + 1];

    if (ch === '(' && next === '*' && !inString) {
      depth++;
      i++;
      continue;
    }
    if (ch === '*' && next === ')' && depth > 0 && !inString) {
      depth--;
      i++;
      continue;
    }
    if (ch === '"' && depth === 0) {
      if (inString && next === '"') {
        i++;
        continue;
      }
      inString = !inString;
    }
  }
  return depth > 0;
}

/**
 * Skips past a `(* ... *)` comment starting at `startPos`.
 *
 * Assumes `code[startPos..startPos+1]` is `(*`. Returns the index
 * immediately after the closing `*)`, handling nesting.
 *
 * @param code - The source code
 * @param startPos - Position of the opening `(`
 * @returns Position after the closing `)`, or `code.length` if unclosed
 */
export function skipCoqComment(code: string, startPos: number): number {
  let depth = 1;
  let pos = startPos + 2;
  while (pos < code.length && depth > 0) {
    if (code[pos] === '(' && pos + 1 < code.length && code[pos + 1] === '*') {
      depth++;
      pos += 2;
    } else if (code[pos] === '*' && pos + 1 < code.length && code[pos + 1] === ')') {
      depth--;
      pos += 2;
    } else {
      pos++;
    }
  }
  return pos;
}

/**
 * Extracts deduplicated hypothesis names from a hypothesis name string.
 *
 * Coq groups hypotheses with the same type, producing names like `"x, y"`.
 * This splits them, trims whitespace, and filters empty strings.
 *
 * @param hypName - Comma-separated hypothesis name string (e.g., `"x, y"`)
 * @returns Array of individual trimmed names
 */
export function splitHypNames(hypName: string): string[] {
  return hypName.split(',').map((n) => n.trim()).filter(Boolean);
}
