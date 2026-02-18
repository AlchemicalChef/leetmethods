/**
 * @module coq-hover
 *
 * CodeMirror 6 hover tooltip extension for Coq tactic documentation and
 * hypothesis type information.
 *
 * When the user hovers over a known Coq tactic, a tooltip displays the
 * tactic's signature, category, description, and related tactics.
 * When hovering over a hypothesis name from the current proof context,
 * the tooltip shows the hypothesis type.
 *
 * @see tactic-docs.ts - Source of tactic documentation displayed in tooltips
 * @see coq-autocomplete.ts - goalsField used for hypothesis lookups
 */
import { hoverTooltip, type Tooltip } from '@codemirror/view';
import { tacticDocMap } from './tactic-docs';
import { goalsField } from './coq-autocomplete';
import { splitHypNames } from './coq-comment';
import { createTooltipContainer, appendMonoHeader, appendGrayLabel } from './tooltip-dom';

/**
 * Extracts the identifier word at a given position in a document line.
 * Returns the word, its start offset, and end offset (all line-relative).
 */
function wordAt(text: string, posInLine: number): { word: string; start: number; end: number } | null {
  let start = posInLine;
  let end = posInLine;
  while (start > 0 && /[a-zA-Z0-9_']/.test(text[start - 1])) start--;
  while (end < text.length && /[a-zA-Z0-9_']/.test(text[end])) end++;
  const word = text.slice(start, end);
  // Must start with a letter or underscore (not a digit)
  if (!word || !/^[a-zA-Z_]/.test(word)) return null;
  return { word, start, end };
}

/**
 * CodeMirror 6 hover tooltip extension for Coq.
 *
 * Checks two sources in order:
 * 1. Tactic documentation (from tacticDocMap)
 * 2. Hypothesis names from the current proof context (from goalsField)
 */
export const coqHoverTooltip = hoverTooltip((view, pos): Tooltip | null => {
  const { from, text } = view.state.doc.lineAt(pos);
  const result = wordAt(text, pos - from);
  if (!result) return null;

  const { word, start, end } = result;

  // Check tactic documentation first
  const doc = tacticDocMap.get(word);
  if (doc) {
    return {
      pos: from + start,
      end: from + end,
      above: true,
      create() {
        const dom = createTooltipContainer();

        appendMonoHeader(dom, doc.signature);
        appendGrayLabel(dom, doc.category);

        const desc = document.createElement('div');
        desc.style.cssText = 'margin-bottom: 6px;';
        desc.textContent = doc.description;
        dom.appendChild(desc);

        if (doc.seeAlso.length > 0) {
          appendGrayLabel(dom, `See also: ${doc.seeAlso.join(', ')}`);
        }

        return { dom };
      },
    };
  }

  // Check hypothesis names from the current proof context
  const goals = view.state.field(goalsField);
  for (const goal of goals) {
    for (const hyp of goal.hypotheses) {
      if (splitHypNames(hyp.name).includes(word)) {
        return {
          pos: from + start,
          end: from + end,
          above: true,
          create() {
            const dom = createTooltipContainer();

            appendGrayLabel(dom, 'Hypothesis');
            appendMonoHeader(dom, `${word} : ${hyp.type}`);

            return { dom };
          },
        };
      }
    }
  }

  return null;
});
