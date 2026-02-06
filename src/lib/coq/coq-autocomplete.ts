import { autocompletion, CompletionContext, type CompletionResult } from '@codemirror/autocomplete';
import { tacticDocs } from './tactic-docs';

function coqCompletions(context: CompletionContext): CompletionResult | null {
  const word = context.matchBefore(/[a-zA-Z_]\w*/);
  if (!word || (word.from === word.to && !context.explicit)) return null;

  const options = tacticDocs
    .filter((doc) => doc.name.startsWith(word.text))
    .map((doc) => ({
      label: doc.name,
      type: 'function' as const,
      detail: doc.signature,
      info: `${doc.description}\n\nExample:\n${doc.example}`,
      boost: doc.name === word.text ? 2 : 0,
    }));

  if (options.length === 0) return null;

  return {
    from: word.from,
    options,
    validFor: /^[a-zA-Z_]\w*$/,
  };
}

export const coqAutocomplete = autocompletion({
  override: [coqCompletions],
  activateOnTyping: true,
  maxRenderedOptions: 15,
});
