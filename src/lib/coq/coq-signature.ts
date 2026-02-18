/**
 * @module coq-signature
 *
 * CodeMirror 6 signature help extension for Coq tactics.
 *
 * Shows a parameter hint tooltip when the cursor is positioned after a
 * known tactic name followed by a space. The tooltip displays the tactic's
 * signature and a brief description.
 *
 * @see tactic-docs.ts - Source of tactic signatures
 */
import { StateField } from '@codemirror/state';
import { showTooltip, type Tooltip } from '@codemirror/view';
import { tacticDocMap } from './tactic-docs';
import { isInsideCoqComment } from './coq-comment';
import { createTooltipContainer, appendMonoHeader, appendGrayLabel } from './tooltip-dom';

/**
 * StateField that computes the current signature tooltip based on cursor position.
 *
 * The tooltip appears when the cursor is right after "tactic " (tactic name
 * followed by at least one space). It disappears when the cursor moves away.
 */
const signatureTooltipField = StateField.define<Tooltip | null>({
  create() {
    return null;
  },

  update(tooltip, tr) {
    if (!tr.docChanged && !tr.selection) return tooltip;

    const state = tr.state;
    const pos = state.selection.main.head;
    const line = state.doc.lineAt(pos);
    const textBefore = line.text.slice(0, pos - line.from);

    // Don't show signature help inside comments
    if (isInsideCoqComment(textBefore, textBefore.length)) return null;

    // Match: optional whitespace, tactic name, one or more spaces (cursor here)
    // The tactic must be at the beginning of a "word context" (after whitespace, period, or start of line)
    const match = textBefore.match(/(?:^|[.\s])\s*([a-zA-Z_]\w*)\s+$/);
    if (!match) return null;

    const tacticName = match[1];
    const doc = tacticDocMap.get(tacticName);
    if (!doc) return null;

    return {
      pos,
      above: true,
      strictSide: true,
      create() {
        const dom = createTooltipContainer();

        appendMonoHeader(dom, doc.signature);

        const desc = document.createElement('div');
        desc.style.cssText = 'opacity: 0.8; font-size: 11px;';
        desc.textContent = doc.description.split('.')[0] + '.';
        dom.appendChild(desc);

        appendGrayLabel(dom, doc.category);

        return { dom };
      },
    };
  },

  provide: (f) => showTooltip.from(f),
});

/**
 * CodeMirror extension for Coq tactic signature help.
 */
export const coqSignatureHelp = signatureTooltipField;
