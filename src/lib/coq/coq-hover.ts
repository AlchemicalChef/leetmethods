import { hoverTooltip, type Tooltip } from '@codemirror/view';
import { tacticDocMap } from './tactic-docs';

export const coqHoverTooltip = hoverTooltip((view, pos): Tooltip | null => {
  const { from, text } = view.state.doc.lineAt(pos);
  // Extract word at position
  let start = pos - from;
  let end = pos - from;

  while (start > 0 && /[a-zA-Z_\w]/.test(text[start - 1])) start--;
  while (end < text.length && /[a-zA-Z_\w]/.test(text[end])) end++;

  const word = text.slice(start, end);
  if (!word) return null;

  const doc = tacticDocMap.get(word);
  if (!doc) return null;

  return {
    pos: from + start,
    end: from + end,
    above: true,
    create() {
      const dom = document.createElement('div');
      dom.style.cssText = 'max-width: 400px; font-size: 13px; line-height: 1.4; padding: 8px 12px;';

      const name = document.createElement('div');
      name.style.cssText = 'font-weight: bold; margin-bottom: 4px; font-family: monospace;';
      name.textContent = doc.signature;
      dom.appendChild(name);

      const category = document.createElement('div');
      category.style.cssText = 'font-size: 11px; opacity: 0.7; margin-bottom: 6px;';
      category.textContent = doc.category;
      dom.appendChild(category);

      const desc = document.createElement('div');
      desc.style.cssText = 'margin-bottom: 6px;';
      desc.textContent = doc.description;
      dom.appendChild(desc);

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
