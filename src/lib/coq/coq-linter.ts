/**
 * @module coq-linter
 *
 * CodeMirror 6 linter for static analysis of Coq source code.
 *
 * Provides inline warnings (yellow squiggles) for:
 * - `Admitted.` usage (proof left unfinished)
 * - `admit.` usage (individual goal left unproven)
 *
 * These are checked statically (text pattern matching) rather than via
 * Coq execution, so they appear immediately as the user types.
 *
 * @see coq-diagnostics.ts - Execution-based error diagnostics
 * @see coq-parser.ts - parseStatements used for context-aware detection
 */
import { linter } from '@codemirror/lint';
import type { Diagnostic } from '@codemirror/lint';
import { isInsideCoqComment } from './coq-comment';

/**
 * CodeMirror linter extension for Coq static analysis warnings.
 *
 * Scans the document for patterns that indicate incomplete proofs:
 * - `Admitted.` — the user gave up on a proof
 * - `admit.` — the user skipped an individual goal
 *
 * Uses isInsideCoqComment to avoid false positives inside comments or strings.
 */
export const coqLinter = linter((view) => {
  const diagnostics: Diagnostic[] = [];
  const text = view.state.doc.toString();

  const patterns: { pattern: string; message: string }[] = [
    { pattern: 'Admitted.', message: 'Proof left unfinished — Admitted skips the proof obligation' },
    { pattern: 'admit.', message: 'Goal left unproven — admit introduces an axiom' },
  ];

  for (const { pattern, message } of patterns) {
    let searchFrom = 0;
    while (searchFrom < text.length) {
      const idx = text.indexOf(pattern, searchFrom);
      if (idx === -1) break;
      searchFrom = idx + pattern.length;

      // Word boundary check
      const before = idx > 0 ? text[idx - 1] : ' ';
      if (/[a-zA-Z0-9_]/.test(before)) continue;

      // Skip matches inside comments or strings
      if (isInsideCoqComment(text, idx)) continue;

      diagnostics.push({
        from: idx,
        to: idx + pattern.length,
        message,
        severity: 'warning',
      });
    }
  }

  return diagnostics;
}, { delay: 500 });
