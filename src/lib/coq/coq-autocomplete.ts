/**
 * @module coq-autocomplete
 *
 * CodeMirror 6 autocomplete extension for Coq.
 *
 * Provides three categories of completions:
 * 1. **Hypothesis completions** — names from the current proof context (H, IHn, etc.)
 * 2. **Context-aware tactic completions** — concrete tactic applications using
 *    hypothesis names (e.g., `rewrite H`, `apply IHn`, `destruct H as []`)
 * 3. **Static tactic completions** — all known tactic names with documentation
 *
 * Uses CM6 snippet templates for tactics that take arguments, placing the cursor
 * inside a placeholder so the user can tab through parameters.
 *
 * @see tactic-docs.ts - Source of tactic documentation used for suggestions
 * @see coq-hover.ts - Hover tooltips for the same editor
 */
import { autocompletion, snippetCompletion } from '@codemirror/autocomplete';
import type { Completion, CompletionContext, CompletionResult } from '@codemirror/autocomplete';
import { StateEffect, StateField } from '@codemirror/state';
import { tacticDocs } from './tactic-docs';
import type { CoqGoal, CoqHypothesis } from './types';
import { splitHypNames } from './coq-comment';

/* ============================================================================
 * Goals StateField
 *
 * Pipes proof context (goals with hypotheses) from React into CodeMirror
 * so the completion source can suggest hypothesis names alongside tactics.
 * ============================================================================ */

/** StateEffect to update the goals stored in the editor state. */
export const setEditorGoals = StateEffect.define<CoqGoal[]>();

/** StateField that holds the current proof goals for use by completions. */
export const goalsField = StateField.define<CoqGoal[]>({
  create() {
    return [];
  },
  update(goals, tr) {
    for (const effect of tr.effects) {
      if (effect.is(setEditorGoals)) {
        return effect.value;
      }
    }
    return goals;
  },
});

/* ============================================================================
 * Snippet Templates
 *
 * Tactic snippets with tab-stop placeholders for common patterns.
 * CM6 snippet syntax: ${n} or ${n:default} for tab stops.
 * ============================================================================ */

const tacticSnippets: { label: string; snippet: string; detail: string; info: string; boost: number }[] = [
  { label: 'intros', snippet: 'intros ${name}', detail: 'intros x y z', info: 'Introduce variables and hypotheses', boost: 0 },
  { label: 'destruct', snippet: 'destruct ${H}', detail: 'destruct H', info: 'Case analysis on a term', boost: 0 },
  { label: 'induction', snippet: 'induction ${n}', detail: 'induction n', info: 'Proof by induction', boost: 0 },
  { label: 'rewrite', snippet: 'rewrite ${H}', detail: 'rewrite H', info: 'Rewrite using an equality hypothesis', boost: 0 },
  { label: 'apply', snippet: 'apply ${H}', detail: 'apply H', info: 'Apply a hypothesis or lemma', boost: 0 },
  { label: 'assert', snippet: 'assert (${H} : ${P})', detail: 'assert (H : P)', info: 'Introduce an intermediate goal', boost: 0 },
  { label: 'unfold', snippet: 'unfold ${def}', detail: 'unfold def', info: 'Expand a definition', boost: 0 },
  { label: 'exists', snippet: 'exists ${witness}', detail: 'exists x', info: 'Provide an existential witness', boost: 0 },
  { label: 'specialize', snippet: 'specialize (${H} ${arg})', detail: 'specialize (H x)', info: 'Instantiate a universally quantified hypothesis', boost: 0 },
  { label: 'remember', snippet: 'remember ${expr} as ${x}', detail: 'remember expr as x', info: 'Name a subexpression', boost: 0 },
  { label: 'replace', snippet: 'replace ${a} with ${b}', detail: 'replace a with b', info: 'Replace a subterm with another', boost: 0 },
  { label: 'exact', snippet: 'exact ${term}', detail: 'exact H', info: 'Provide the exact proof term', boost: 0 },
  { label: 'revert', snippet: 'revert ${x}', detail: 'revert x', info: 'Move a hypothesis back into the goal', boost: 0 },
  { label: 'rename', snippet: 'rename ${old} into ${new}', detail: 'rename H into H0', info: 'Rename a hypothesis', boost: 0 },
  { label: 'set', snippet: 'set (${x} := ${expr})', detail: 'set (x := expr)', info: 'Name a subexpression with a local definition', boost: 0 },
  { label: 'pose', snippet: 'pose (${x} := ${expr})', detail: 'pose (x := expr)', info: 'Introduce a local definition', boost: 0 },
];

/** Set of tactic names that have snippet versions (to avoid duplicate plain completions) */
const snippetTacticNames = new Set(tacticSnippets.map(s => s.label));

/* ============================================================================
 * Context-Aware Tactic Completions
 *
 * Generate concrete completions like "rewrite H" or "apply IHn" based on
 * actual hypothesis names and types in the current proof context.
 * ============================================================================ */

/**
 * Extracts deduplicated hypothesis names from the current goals.
 */
function extractHypotheses(goals: CoqGoal[]): { name: string; hyp: CoqHypothesis }[] {
  const seen = new Set<string>();
  const result: { name: string; hyp: CoqHypothesis }[] = [];
  for (const goal of goals) {
    for (const hyp of goal.hypotheses) {
      for (const name of splitHypNames(hyp.name)) {
        if (!seen.has(name)) {
          seen.add(name);
          result.push({ name, hyp });
        }
      }
    }
  }
  return result;
}

/**
 * Generates context-aware tactic completions from hypothesis names.
 * E.g., "rewrite H" when H has an equality type, "apply H" when H's
 * conclusion matches the goal, "destruct H" for sum/product types, etc.
 */
function contextAwareTacticCompletions(goals: CoqGoal[], prefix: string): Completion[] {
  if (goals.length === 0) return [];
  const hyps = extractHypotheses(goals);
  const completions: Completion[] = [];
  const seen = new Set<string>();

  for (const { name, hyp } of hyps) {
    // rewrite H — when H has an equality type
    if (hyp.type.includes('=')) {
      const label = `rewrite ${name}`;
      if (label.startsWith(prefix) && !seen.has(label)) {
        seen.add(label);
        completions.push({ label, type: 'function', detail: hyp.type, info: `Rewrite using ${name}`, boost: 3 });
      }
      const labelRev = `rewrite <- ${name}`;
      if (labelRev.startsWith(prefix) && !seen.has(labelRev)) {
        seen.add(labelRev);
        completions.push({ label: labelRev, type: 'function', detail: hyp.type, info: `Rewrite ${name} right-to-left`, boost: 3 });
      }
    }

    // apply H — when H has an implication or matches the goal
    if (hyp.type.includes('->') || hyp.type.startsWith('forall')) {
      const label = `apply ${name}`;
      if (label.startsWith(prefix) && !seen.has(label)) {
        seen.add(label);
        completions.push({ label, type: 'function', detail: hyp.type, info: `Apply ${name} to the goal`, boost: 3 });
      }
    }

    // destruct H — for any hypothesis
    const destructLabel = `destruct ${name}`;
    if (destructLabel.startsWith(prefix) && !seen.has(destructLabel)) {
      seen.add(destructLabel);
      completions.push({ label: destructLabel, type: 'function', detail: hyp.type, info: `Case analysis on ${name}`, boost: 2 });
    }

    // inversion H — for inductive hypothesis types
    const invLabel = `inversion ${name}`;
    if (invLabel.startsWith(prefix) && !seen.has(invLabel)) {
      seen.add(invLabel);
      completions.push({ label: invLabel, type: 'function', detail: hyp.type, info: `Invert ${name}`, boost: 1 });
    }

    // exact H — for any hypothesis
    const exactLabel = `exact ${name}`;
    if (exactLabel.startsWith(prefix) && !seen.has(exactLabel)) {
      seen.add(exactLabel);
      completions.push({ label: exactLabel, type: 'function', detail: hyp.type, info: `Provide ${name} as the exact proof`, boost: 2 });
    }
  }

  return completions;
}

/* ============================================================================
 * Completion Source
 * ============================================================================ */

/**
 * CodeMirror completion source for Coq.
 *
 * Returns merged completions from:
 * 1. Hypothesis names (boost: 5)
 * 2. Context-aware tactic applications (boost: 2-3)
 * 3. Snippet templates (with tab stops)
 * 4. Static tactic documentation entries (boost: 0-2)
 */
function coqCompletions(context: CompletionContext): CompletionResult | null {
  const word = context.matchBefore(/[a-zA-Z_][\w']*/);

  if (!word || (word.from === word.to && !context.explicit)) return null;

  const goals = context.state.field(goalsField);

  // 1. Hypothesis name completions
  const seen = new Set<string>();
  const hypOptions: Completion[] = [];
  for (const goal of goals) {
    for (const hyp of goal.hypotheses) {
      for (const name of splitHypNames(hyp.name)) {
        if (!seen.has(name) && name.startsWith(word.text)) {
          seen.add(name);
          hypOptions.push({ label: name, type: 'variable', detail: hyp.type, boost: 5 });
        }
      }
    }
  }

  // 2. Context-aware tactic completions (rewrite H, apply H, etc.)
  const contextOptions = contextAwareTacticCompletions(goals, word.text);

  // 3. Snippet completions (tactic templates with tab stops)
  const snippetOptions: Completion[] = tacticSnippets
    .filter((s) => s.label.startsWith(word.text))
    .map((s) => snippetCompletion(s.snippet, {
      label: s.label,
      type: 'function',
      detail: s.detail,
      info: s.info,
      boost: s.boost,
    }));

  // 4. Static tactic completions (skip those that have snippet versions)
  const tacticOptions: Completion[] = tacticDocs
    .filter((doc) => doc.name.startsWith(word.text) && !snippetTacticNames.has(doc.name))
    .map((doc) => ({
      label: doc.name,
      type: 'function' as const,
      detail: doc.signature,
      info: `${doc.description}\n\nExample:\n${doc.example}`,
      boost: doc.name === word.text ? 2 : 0,
    }));

  const options = [...hypOptions, ...contextOptions, ...snippetOptions, ...tacticOptions];

  if (options.length === 0) return null;

  return {
    from: word.from,
    options,
    validFor: /^[a-zA-Z_][\w']*$/,
  };
}

/**
 * Pre-configured CodeMirror autocompletion extension for Coq.
 *
 * Includes the goalsField StateField so context-aware completions work.
 */
export const coqAutocomplete = [
  goalsField,
  autocompletion({
    override: [coqCompletions],
    activateOnTyping: true,
    maxRenderedOptions: 15,
  }),
];
