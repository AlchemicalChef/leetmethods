/**
 * @module coq-diagnostics
 *
 * Pure helpers for computing inline editor diagnostics from Coq execution errors.
 *
 * When a Coq statement fails (e.g., a tactic doesn't apply), this module
 * computes the character range of the failing statement so that CodeMirror
 * can display a red squiggly underline on it.
 *
 * @see coq-parser.ts - parseStatements() used to locate statement boundaries
 * @see CoqEditor.tsx - Consumes diagnostics via setDiagnostics from @codemirror/lint
 */
import { parseStatements } from './coq-parser';
import { skipCoqComment } from './coq-comment';

/**
 * Finds the position of a statement in the code starting from `offset`,
 * skipping over comments and whitespace so we don't match text inside
 * `(* ... *)` comment blocks.
 */
function findStatementPos(code: string, stmt: string, offset: number): number {
  let pos = offset;
  while (pos < code.length) {
    if (/\s/.test(code[pos])) { pos++; continue; }
    if (code[pos] === '(' && pos + 1 < code.length && code[pos + 1] === '*') {
      pos = skipCoqComment(code, pos);
      continue;
    }
    if (code.startsWith(stmt, pos)) return pos;
    break;
  }
  return code.indexOf(stmt, offset);
}

/**
 * A diagnostic representing a Coq error at a specific source range.
 *
 * The `from` and `to` offsets are relative to the user's code (not including
 * the prelude), matching the CodeMirror document coordinates.
 */
export interface CoqDiagnostic {
  /** Start character offset in user code */
  from: number;
  /** End character offset in user code */
  to: number;
  /** Error message to display */
  message: string;
  /** Diagnostic severity */
  severity: 'error' | 'warning';
}

/**
 * Computes a diagnostic for a failing Coq statement.
 *
 * Uses `parseStatements()` to find the character range of the statement at
 * `failingIndex` in the full code (prelude + user code). The prelude offset
 * is subtracted to produce user-code-relative coordinates.
 *
 * @param fullCode - The full code sent to Coq (prelude + "\n\n" + userCode)
 * @param failingIndex - 0-based index of the failing statement in the full code's
 *   parsed statement list (i.e., the number of successfully executed statements)
 * @param preludeLength - Character length of the prelude (before the "\n\n" separator)
 * @param errorMsg - The error message from Coq
 * @returns A CoqDiagnostic with user-code-relative offsets, or null if the error
 *   is in the prelude or the index is out of range
 */
export function computeErrorDiagnostic(
  fullCode: string,
  failingIndex: number,
  preludeLength: number,
  errorMsg: string,
): CoqDiagnostic | null {
  const statements = parseStatements(fullCode);

  if (failingIndex < 0 || failingIndex >= statements.length) return null;

  // Walk through statements to find character offsets
  let offset = 0;
  for (let i = 0; i <= failingIndex; i++) {
    const idx = findStatementPos(fullCode, statements[i], offset);
    if (idx === -1) return null;
    if (i === failingIndex) {
      const stmtFrom = idx;
      const stmtTo = idx + statements[i].length;
      // The prelude offset includes the "\n\n" separator (2 chars)
      const preludeOffset = preludeLength + 2;

      // If the failing statement is within the prelude, skip
      if (stmtTo <= preludeOffset) return null;

      return {
        from: Math.max(0, stmtFrom - preludeOffset),
        to: Math.max(0, stmtTo - preludeOffset),
        message: errorMsg,
        severity: 'error',
      };
    }
    offset = idx + statements[i].length;
  }

  return null;
}
