/**
 * @module coq-closebracket
 *
 * CodeMirror 6 input handler that auto-closes Coq comment delimiters.
 *
 * When the user types `(*`, this extension automatically inserts ` *)` after
 * the cursor, placing the cursor between the delimiters for easy comment entry.
 *
 * @see coq-syntax.ts - Syntax highlighting that handles comments
 */
import { EditorView } from '@codemirror/view';

/**
 * Input handler that watches for `(*` being typed and auto-inserts ` *)`.
 *
 * Implementation: when a `*` is inserted and the character before it is `(`,
 * we have a `(*` sequence. Insert `  *)` (space, space, star, paren) and
 * move the cursor to the space between `(*` and `*)`.
 */
export const coqCommentClose = EditorView.inputHandler.of((view, from, to, text) => {
  if (text !== '*') return false;

  // Check if the character before the insertion point is `(`
  if (from === 0) return false;
  const charBefore = view.state.doc.sliceString(from - 1, from);
  if (charBefore !== '(') return false;

  // Don't auto-close if we're already inside a comment (next char is `*`)
  if (to < view.state.doc.length) {
    const charAfter = view.state.doc.sliceString(to, to + 1);
    if (charAfter === '*') return false;
  }

  // We're typing `(*` — auto-insert ` *)`
  // Result: `(*| *)` where | is the cursor
  view.dispatch({
    changes: [
      { from, to, insert: '*  *)' },
    ],
    selection: { anchor: from + 2 },
  });
  return true;
});
