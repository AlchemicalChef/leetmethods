/**
 * @module tooltip-dom
 *
 * Shared DOM helpers for CodeMirror 6 tooltip creation in Coq extensions.
 *
 * Both coq-hover.ts and coq-signature.ts build tooltip DOM trees with
 * the same structure and styles. These helpers eliminate the duplication.
 *
 * @see coq-hover.ts - Tactic docs and hypothesis hover tooltips
 * @see coq-signature.ts - Tactic parameter signature tooltips
 */

/**
 * Creates the standard tooltip container div with consistent styling.
 */
export function createTooltipContainer(): HTMLDivElement {
  const dom = document.createElement('div');
  dom.style.cssText = 'max-width: 400px; font-size: 13px; line-height: 1.4; padding: 8px 12px;';
  return dom;
}

/**
 * Appends a bold monospace header element (used for tactic signatures and hypothesis types).
 */
export function appendMonoHeader(parent: HTMLElement, text: string): void {
  const el = document.createElement('div');
  el.style.cssText = 'font-weight: bold; margin-bottom: 4px; font-family: monospace;';
  el.textContent = text;
  parent.appendChild(el);
}

/**
 * Appends a small gray label element (used for categories, "Hypothesis" labels, "See also").
 */
export function appendGrayLabel(parent: HTMLElement, text: string): void {
  const el = document.createElement('div');
  el.style.cssText = 'font-size: 11px; opacity: 0.7; margin-bottom: 4px;';
  el.textContent = text;
  parent.appendChild(el);
}
