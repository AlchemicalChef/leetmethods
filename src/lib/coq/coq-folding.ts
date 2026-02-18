/**
 * @module coq-folding
 *
 * CodeMirror 6 fold service for Coq source code.
 *
 * Provides folding ranges for:
 * - Proof...Qed/Defined/Admitted blocks
 * - Multi-line (* ... *) comments (including nested)
 *
 * @see coq-syntax.ts - Syntax highlighting for the same editor
 */
import { foldService } from '@codemirror/language';
import { foldGutter } from '@codemirror/language';

/**
 * Fold service that detects foldable ranges at a given line.
 *
 * For a line starting with "Proof", finds the matching "Qed", "Defined",
 * or "Admitted" and returns the fold range.
 *
 * For a line containing "(*", finds the matching "*)" accounting for
 * nesting and returns the fold range.
 */
const coqFoldService = foldService.of((state, lineStart) => {
  const line = state.doc.lineAt(lineStart);
  const text = line.text.trimStart();

  // Fold Proof...Qed/Defined/Admitted blocks (with depth tracking for nesting)
  if (/^Proof\b/.test(text)) {
    let depth = 1;
    for (let i = line.number + 1; i <= state.doc.lines; i++) {
      const nextLine = state.doc.line(i);
      const nextText = nextLine.text.trimStart();
      if (/^Proof\b/.test(nextText)) {
        depth++;
      } else if (/^(Qed|Defined|Admitted)\s*\./.test(nextText)) {
        depth--;
        if (depth === 0) {
          return { from: line.to, to: nextLine.to };
        }
      }
    }
  }

  // Fold multi-line (* ... *) comments
  // Find the first `(*` on the line that starts an unclosed comment
  const commentStart = line.text.indexOf('(*');
  if (commentStart !== -1) {
    const docPos = line.from + commentStart;
    let depth = 0;
    const scanLimit = Math.min(state.doc.length, docPos + 100_000);
    for (let pos = docPos; pos < scanLimit - 1; pos++) {
      const ch = state.doc.sliceString(pos, pos + 2);
      if (ch === '(*') {
        depth++;
        pos++; // skip past the *
      } else if (ch === '*)') {
        depth--;
        if (depth === 0) {
          const endPos = pos + 2;
          // Only fold if the comment spans multiple lines
          const endLine = state.doc.lineAt(endPos);
          if (endLine.number > line.number) {
            return { from: docPos + 2, to: endPos };
          }
          return null;
        }
        pos++; // skip past the )
      }
    }
  }

  return null;
});

/**
 * CodeMirror extension array for Coq code folding.
 * Includes both the fold service (logic) and fold gutter (UI).
 */
export const coqFolding = [
  coqFoldService,
  foldGutter(),
];
