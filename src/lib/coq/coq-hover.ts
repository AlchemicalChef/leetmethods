/**
 * @module coq-hover
 *
 * CodeMirror 6 hover tooltip extension for Coq tactic documentation.
 *
 * When the user hovers over a known Coq tactic in the editor, this extension
 * displays a tooltip with the tactic's signature, category, description, and
 * related tactics. This provides inline documentation without leaving the editor.
 *
 * ## How It Works
 *
 * 1. CodeMirror fires the hover handler with the cursor position.
 * 2. The handler extracts the word at the hover position by scanning for
 *    word characters in both directions from the cursor.
 * 3. The word is looked up in the `tacticDocMap` (from `tactic-docs.ts`).
 * 4. If found, a tooltip is created with a DOM-based layout showing:
 *    - **Signature** (monospace, bold): e.g., `intros x y z`
 *    - **Category** (small, dimmed): e.g., `Introduction`
 *    - **Description**: Full explanation of what the tactic does
 *    - **See also** (small, dimmed): Related tactics
 *
 * ## Design Decisions
 *
 * - The tooltip is positioned `above: true` to avoid overlapping with the
 *   goals panel which is typically below the editor.
 * - The tooltip DOM is constructed manually rather than using React because
 *   CodeMirror's tooltip API expects a plain DOM element. This keeps the
 *   tooltip lightweight and avoids pulling in the React rendering pipeline.
 * - The word extraction uses a simple character-by-character scan rather than
 *   a regex on the full line, which is more efficient for long lines.
 * - Max width is set to 400px to keep tooltips readable without being too wide.
 *
 * @see tactic-docs.ts - Source of tactic documentation displayed in tooltips
 * @see coq-autocomplete.ts - Autocomplete integration for the same editor
 * @see coq-syntax.ts - Syntax highlighting for the same editor
 */
import { hoverTooltip, type Tooltip } from '@codemirror/view';
import { tacticDocMap } from './tactic-docs';

/**
 * CodeMirror 6 hover tooltip extension for Coq tactics.
 *
 * Register this in the editor's extensions array to enable hover documentation.
 * When the user hovers over a recognized tactic name, a tooltip appears with
 * its documentation.
 *
 * @example
 * ```ts
 * import { coqHoverTooltip } from './coq-hover';
 * const editor = new EditorView({
 *   extensions: [coqHoverTooltip, ...otherExtensions],
 * });
 * ```
 */
export const coqHoverTooltip = hoverTooltip((view, pos): Tooltip | null => {
  const { from, text } = view.state.doc.lineAt(pos);

  // Extract the word at the hover position by scanning outward from the
  // cursor position for word characters (letters, digits, underscores).
  // `start` and `end` are offsets within the line text (not document positions).
  let start = pos - from;
  let end = pos - from;

  // Scan backward to find the start of the word
  while (start > 0 && /[a-zA-Z_\w]/.test(text[start - 1])) start--;
  // Scan forward to find the end of the word
  while (end < text.length && /[a-zA-Z_\w]/.test(text[end])) end++;

  const word = text.slice(start, end);
  if (!word) return null;

  // Look up the word in the tactic documentation map
  const doc = tacticDocMap.get(word);
  if (!doc) return null;

  return {
    // Convert line-relative offsets back to absolute document positions
    pos: from + start,
    end: from + end,
    // Position tooltip above the text to avoid overlapping with the goals panel
    above: true,
    /**
     * Creates the tooltip DOM element. This is called lazily by CodeMirror
     * only when the tooltip needs to be displayed.
     *
     * The tooltip layout:
     * ```
     * +----------------------------------+
     * | intros x y z                     |  <- signature (monospace, bold)
     * | Introduction                     |  <- category (small, dimmed)
     * |                                  |
     * | Introduces variables and hyps... |  <- description
     * |                                  |
     * | See also: intro, revert          |  <- related tactics (small, dimmed)
     * +----------------------------------+
     * ```
     */
    create() {
      const dom = document.createElement('div');
      dom.style.cssText = 'max-width: 400px; font-size: 13px; line-height: 1.4; padding: 8px 12px;';

      // Tactic signature in monospace bold (e.g., "intros x y z")
      const name = document.createElement('div');
      name.style.cssText = 'font-weight: bold; margin-bottom: 4px; font-family: monospace;';
      name.textContent = doc.signature;
      dom.appendChild(name);

      // Category label (e.g., "Introduction", "Rewriting", "Case Analysis")
      const category = document.createElement('div');
      category.style.cssText = 'font-size: 11px; opacity: 0.7; margin-bottom: 6px;';
      category.textContent = doc.category;
      dom.appendChild(category);

      // Full description of what the tactic does
      const desc = document.createElement('div');
      desc.style.cssText = 'margin-bottom: 6px;';
      desc.textContent = doc.description;
      dom.appendChild(desc);

      // "See also" section listing related tactics (only shown if there are any)
      if (doc.seeAlso.length > 0) {
        const seeAlso = document.createElement('div');
        seeAlso.style.cssText = 'font-size: 11px; opacity: 0.7;';
        seeAlso.textContent = `See also: ${doc.seeAlso.join(', ')}`;
        dom.appendChild(seeAlso);
      }

      return { dom };
    },
  };
});
