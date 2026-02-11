/**
 * @module coq-autocomplete
 *
 * CodeMirror 6 autocomplete extension for Coq tactic names.
 *
 * Provides inline autocomplete suggestions as the user types Coq tactics in
 * the editor. Suggestions are sourced from the `tacticDocs` array in
 * `tactic-docs.ts`, which contains documentation for all known Coq tactics.
 *
 * ## How It Works
 *
 * 1. As the user types, CodeMirror calls `coqCompletions()` with the current
 *    cursor context.
 * 2. The function matches the word being typed against all known tactic names
 *    using a prefix match (`startsWith`).
 * 3. Matching tactics are returned as completion options with their signature
 *    as the detail line and their description + example as the info popup.
 * 4. Exact matches get a boost score of 2 to appear first in the list.
 *
 * ## Design Decisions
 *
 * - Uses prefix matching rather than fuzzy matching for simplicity and to
 *   avoid suggesting unrelated tactics. Coq tactic names are short and
 *   distinctive enough that prefix matching works well.
 * - Activates on typing (not just on explicit Ctrl+Space) for a smoother
 *   experience, since Coq tactics are the primary thing users type.
 * - Limits to 15 rendered options to keep the popup manageable.
 * - Returns null (no suggestions) when no tactics match, rather than showing
 *   an empty popup.
 *
 * @see tactic-docs.ts - Source of tactic documentation used for suggestions
 * @see coq-syntax.ts - Syntax highlighting for the same editor
 * @see coq-hover.ts - Hover tooltips for the same editor
 */
import { autocompletion } from '@codemirror/autocomplete';
import type { CompletionContext, CompletionResult } from '@codemirror/autocomplete';
import { tacticDocs } from './tactic-docs';

/**
 * CodeMirror completion source for Coq tactics.
 *
 * Called by CodeMirror whenever the user types or explicitly requests
 * completions (Ctrl+Space). Matches the word at the cursor against known
 * tactic names and returns matching options.
 *
 * @param context - CodeMirror's completion context with cursor position and text
 * @returns CompletionResult with matching options, or null if no matches
 */
function coqCompletions(context: CompletionContext): CompletionResult | null {
  // Match the identifier-like word being typed at the cursor position.
  // Coq identifiers start with a letter or underscore, followed by word characters.
  const word = context.matchBefore(/[a-zA-Z_]\w*/);

  // Don't show completions if there's no word being typed, unless the user
  // explicitly triggered completion (Ctrl+Space / context.explicit)
  if (!word || (word.from === word.to && !context.explicit)) return null;

  // Filter tactic documentation entries to those matching the typed prefix
  const options = tacticDocs
    .filter((doc) => doc.name.startsWith(word.text))
    .map((doc) => ({
      label: doc.name,
      type: 'function' as const,
      detail: doc.signature,
      info: `${doc.description}\n\nExample:\n${doc.example}`,
      // Exact matches are boosted to appear first in the completion list
      boost: doc.name === word.text ? 2 : 0,
    }));

  // Return null instead of an empty result to hide the completion popup
  if (options.length === 0) return null;

  return {
    from: word.from,
    options,
    // Validation regex: keep showing these completions as long as the user
    // continues typing an identifier. If they type a non-identifier character,
    // the completion popup is dismissed.
    validFor: /^[a-zA-Z_]\w*$/,
  };
}

/**
 * Pre-configured CodeMirror autocompletion extension for Coq.
 *
 * Drop this into a CodeMirror editor's extensions array to enable
 * Coq tactic autocompletion.
 *
 * Configuration:
 * - `override`: Replaces the default completion sources with our Coq-specific one
 * - `activateOnTyping`: Shows completions automatically as the user types
 * - `maxRenderedOptions`: Caps the dropdown at 15 items for readability
 */
export const coqAutocomplete = autocompletion({
  override: [coqCompletions],
  activateOnTyping: true,
  maxRenderedOptions: 15,
});
