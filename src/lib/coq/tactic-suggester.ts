/**
 * @module tactic-suggester
 *
 * Intelligent Coq tactic suggestion engine.
 *
 * This module analyzes the current proof state (goals and hypotheses) and
 * suggests up to 3 tactics that are likely to make progress. Suggestions are
 * ranked by confidence level (high, medium, low) and each comes with a
 * human-readable reason explaining why that tactic might help.
 *
 * ## How It Works
 *
 * The suggester uses a **rule-based pattern matching** approach. Each rule
 * inspects the structure of the current goal (its conclusion and hypotheses)
 * and checks for patterns that indicate a particular tactic would be useful:
 *
 * - **High confidence**: Structural matches where the tactic is almost certainly
 *   the right next step (e.g., `split` when the goal is a conjunction `/\`)
 * - **Medium confidence**: Heuristic matches where the tactic is likely helpful
 *   but might not be the only option (e.g., `induction` when the goal involves `nat`)
 * - **Low confidence**: Generic tactics that are always worth trying (e.g., `simpl`, `auto`)
 *
 * Rules are evaluated in order (high -> medium -> low), and the first
 * `MAX_SUGGESTIONS` (3) matching rules are returned. Duplicate tactics and
 * forbidden tactics are skipped.
 *
 * ## Design Decisions
 *
 * - Pattern matching is done on the **text representation** of goals (strings),
 *   not on the AST. This is simpler and sufficient for the common patterns we
 *   need to detect, but means we occasionally miss edge cases (e.g., parenthesized
 *   conjunctions or operator precedence issues).
 * - Each suggestion includes a reference to the tactic's documentation entry
 *   from `tactic-docs.ts`, so the UI can show full documentation on click.
 * - The forbidden tactics list is passed in from the problem definition, allowing
 *   different problems to restrict different tactics (e.g., requiring manual
 *   proof without `auto`).
 *
 * @see CoqGoal - The goal structure analyzed by rules
 * @see tactic-docs.ts - Documentation entries linked to suggestions
 * @see ProblemSolver component - UI that displays suggestions to users
 */
import type { CoqGoal } from './types';
import { tacticDocMap } from './tactic-docs';
import type { TacticDoc } from './tactic-docs';

/* ==============================================================================
 * Types
 * =========================================================================== */

/**
 * Confidence level for a tactic suggestion.
 * - `high`: The tactic almost certainly applies based on the goal structure
 * - `medium`: The tactic is likely to help but alternatives may exist
 * - `low`: A generic tactic worth trying when nothing specific matches
 */
export type Confidence = 'high' | 'medium' | 'low';

/**
 * A single tactic suggestion with its justification and documentation.
 */
export interface TacticSuggestion {
  /** The tactic command to suggest (e.g., "split", "intros", "rewrite") */
  tactic: string;

  /** Human-readable explanation of why this tactic is suggested */
  reason: string;

  /** How confident the engine is that this tactic will help */
  confidence: Confidence;

  /** Link to the full documentation entry for this tactic, or null if not found */
  doc: TacticDoc | null;
}

/**
 * Input context for the suggestion engine.
 * Contains the current proof goals and any tactics that should be excluded.
 */
interface SuggestionContext {
  /** Current proof goals from jsCoq (the first goal is the one being analyzed) */
  goals: CoqGoal[];

  /** Tactics that the problem forbids (these will be excluded from suggestions) */
  forbiddenTactics?: string[];
}

/** Maximum number of suggestions to return */
const MAX_SUGGESTIONS = 3;

/**
 * Internal rule definition. Each rule has a match predicate that inspects
 * a goal and returns true if the associated tactic is applicable.
 */
interface Rule {
  /** Confidence level assigned to suggestions from this rule */
  confidence: Confidence;

  /** Predicate that checks whether this rule applies to the given goal */
  match: (goal: CoqGoal) => boolean;

  /** The tactic to suggest if the rule matches */
  tactic: string;

  /** Human-readable reason explaining why this tactic helps */
  reason: string;
}

/* ==============================================================================
 * High Confidence Rules
 * ==============================================================================
 * These rules match on clear structural properties of the goal conclusion or
 * hypotheses. When they match, the suggested tactic is almost always the
 * correct next step.
 * =========================================================================== */

const highConfidenceRules: Rule[] = [
  {
    // Goal is a conjunction: `A /\ B` or `A ^ B` (Unicode)
    // The `split` tactic breaks this into two subgoals: prove A, then prove B
    confidence: 'high',
    match: (g) => g.conclusion.includes('/\\') || g.conclusion.includes('\u2227'),
    tactic: 'split',
    reason: 'Your goal is a conjunction - use split to break it into two subgoals',
  },
  {
    // Goal is a disjunction: `A \/ B` or `A v B` (Unicode)
    // The `left` tactic commits to proving the first disjunct A
    confidence: 'high',
    match: (g) => g.conclusion.includes('\\/') || g.conclusion.includes('\u2228'),
    tactic: 'left',
    reason: 'Your goal is a disjunction - use left to prove the first disjunct',
  },
  {
    // Goal is a disjunction (same pattern as above but suggests `right`)
    // The `right` tactic commits to proving the second disjunct B
    confidence: 'high',
    match: (g) => g.conclusion.includes('\\/') || g.conclusion.includes('\u2228'),
    tactic: 'right',
    reason: 'Your goal is a disjunction - use right to prove the second disjunct',
  },
  {
    // Goal starts with `forall` (universal quantifier) or contains `->` (implication)
    // The `intros` tactic introduces bound variables and hypothesis premises
    // into the proof context
    confidence: 'high',
    match: (g) => g.conclusion.startsWith('forall') || g.conclusion.includes('->'),
    tactic: 'intros',
    reason: 'Your goal has a universal quantifier or implication - introduce variables/hypotheses',
  },
  {
    // Goal starts with `exists` or contains the Unicode existential quantifier
    // The `exists` tactic requires providing a witness value
    confidence: 'high',
    match: (g) => g.conclusion.startsWith('exists') || g.conclusion.includes('\u2203'),
    tactic: 'exists',
    reason: 'Your goal is existential - provide a witness with exists',
  },
  {
    // Goal is an equality where both sides are textually identical: `X = X`
    // The `reflexivity` tactic solves this immediately
    confidence: 'high',
    match: (g) => {
      const c = g.conclusion.trim();
      const eqMatch = c.match(/^(.+)\s*=\s*(.+)$/);
      if (!eqMatch) return false;
      return eqMatch[1].trim() === eqMatch[2].trim();
    },
    tactic: 'reflexivity',
    reason: 'Both sides of the equality are the same - reflexivity solves this',
  },
  {
    // Goal is the proposition `True`
    // `exact I` provides the canonical proof of True directly
    confidence: 'high',
    match: (g) => g.conclusion.trim() === 'True',
    tactic: 'exact I',
    reason: 'The goal is True - exact I provides the proof directly',
  },
  {
    // A hypothesis has type `False`
    // `contradiction` derives anything from False (ex falso quodlibet)
    confidence: 'high',
    match: (g) => g.hypotheses.some((h) => h.type.trim() === 'False'),
    tactic: 'contradiction',
    reason: 'You have False as a hypothesis - contradiction solves any goal',
  },
  {
    // Goal has the form `S x = S y` where x and y are different
    // `f_equal` strips the common constructor to leave `x = y`
    // (Only suggests when sides differ, since reflexivity handles `S x = S x`)
    confidence: 'high',
    match: (g) => {
      const c = g.conclusion.trim();
      const m = c.match(/^S\s*(.+)\s*=\s*S\s*(.+)$/);
      return !!m && m[1].trim() !== m[2].trim();
    },
    tactic: 'f_equal',
    reason: 'Both sides have the same constructor - f_equal strips it away',
  },
];

/* ==============================================================================
 * Medium Confidence Rules
 * ==============================================================================
 * These rules match on heuristic properties where the suggested tactic is
 * a reasonable next step but might not be the only option.
 * =========================================================================== */

const mediumConfidenceRules: Rule[] = [
  {
    // A hypothesis contains an equality (e.g., `H : x = y`)
    // `rewrite` can substitute this equality into the goal
    confidence: 'medium',
    match: (g) => g.hypotheses.some((h) => {
      const eqMatch = h.type.match(/^(.+)\s*=\s*(.+)$/);
      return !!eqMatch;
    }),
    tactic: 'rewrite',
    reason: 'You have an equality hypothesis - rewrite can substitute it into the goal',
  },
  {
    // A hypothesis type exactly matches the goal conclusion
    // `assumption` solves the goal immediately by citing the matching hypothesis
    confidence: 'medium',
    match: (g) => g.hypotheses.some((h) => h.type.trim() === g.conclusion.trim()),
    tactic: 'assumption',
    reason: 'A hypothesis exactly matches the goal - assumption solves it',
  },
  {
    // A hypothesis has the form `... -> ... -> G` where G matches the goal
    // `apply` uses this hypothesis to reduce the goal to its premises
    confidence: 'medium',
    match: (g) => g.hypotheses.some((h) => {
      const parts = h.type.split('->');
      if (parts.length < 2) return false;
      return parts[parts.length - 1].trim() === g.conclusion.trim();
    }),
    tactic: 'apply',
    reason: 'A hypothesis concludes with your goal - apply it to make progress',
  },
  {
    // The goal or a hypothesis involves `nat` (natural numbers)
    // Induction on nat is one of the most common proof strategies
    confidence: 'medium',
    match: (g) => g.conclusion.includes('nat') || g.hypotheses.some((h) => h.type.includes('nat')),
    tactic: 'induction',
    reason: 'The goal involves natural numbers - induction is often the right strategy',
  },
  {
    // The goal or a hypothesis involves `list`
    // Structural induction on lists is a standard approach
    confidence: 'medium',
    match: (g) => g.conclusion.includes('list') || g.hypotheses.some((h) => h.type.includes('list')),
    tactic: 'induction',
    reason: 'The goal involves lists - structural induction is a common approach',
  },
];

/* ==============================================================================
 * Low Confidence Rules
 * ==============================================================================
 * Generic tactics that are always applicable. These serve as fallback
 * suggestions when no higher-confidence rule matches. They always match
 * (the predicate returns true unconditionally).
 * =========================================================================== */

const lowConfidenceRules: Rule[] = [
  {
    // `simpl` reduces definitions and performs beta/iota/zeta reductions
    // Often makes the goal more readable even if it doesn't solve it
    confidence: 'low',
    match: () => true,
    tactic: 'simpl',
    reason: 'Try simplifying - simpl reduces definitions and computations',
  },
  {
    // `auto` combines simple tactics (apply, assumption, intro, etc.)
    // Can sometimes solve goals that seem complex but are actually routine
    confidence: 'low',
    match: () => true,
    tactic: 'auto',
    reason: 'Try auto - it combines simple tactics to solve easy goals',
  },
];

/* ==============================================================================
 * Suggestion Engine
 * =========================================================================== */

/**
 * Analyzes the current proof state and suggests up to 3 tactics.
 *
 * The engine evaluates rules in priority order (high -> medium -> low),
 * skipping any tactics that are forbidden by the problem or that have
 * already been suggested (deduplication). It stops as soon as
 * `MAX_SUGGESTIONS` (3) suggestions have been collected.
 *
 * Each suggestion includes:
 * - The tactic command string
 * - A human-readable reason
 * - A confidence level
 * - A link to the full tactic documentation (if available)
 *
 * @param context - The current proof state including goals and forbidden tactics
 * @returns Array of tactic suggestions (up to MAX_SUGGESTIONS), ordered by confidence
 *
 * @example
 * ```ts
 * const suggestions = suggestTactics({
 *   goals: [{ id: 1, hypotheses: [], conclusion: "True /\\ False" }],
 *   forbiddenTactics: ["admit"],
 * });
 * // Returns: [{ tactic: "split", confidence: "high", reason: "...", doc: {...} }]
 * ```
 */
export function suggestTactics(context: SuggestionContext): TacticSuggestion[] {
  // No goals means the proof is either complete or not started
  if (context.goals.length === 0) return [];

  // Analyze only the first (current) goal -- Coq works on one goal at a time
  const goal = context.goals[0];

  // Build a set of forbidden tactic names (case-insensitive) for fast lookup
  const forbidden = new Set((context.forbiddenTactics ?? []).map((t) => t.toLowerCase()));

  // Track which tactics have already been suggested to avoid duplicates
  // (e.g., `induction` could match both the nat and list rules)
  const seen = new Set<string>();
  const suggestions: TacticSuggestion[] = [];

  // Concatenate all rules in priority order: high, then medium, then low.
  // Iteration stops when MAX_SUGGESTIONS is reached, ensuring high-confidence
  // suggestions always take priority over lower-confidence ones.
  const allRules = [...highConfidenceRules, ...mediumConfidenceRules, ...lowConfidenceRules];

  for (const rule of allRules) {
    if (suggestions.length >= MAX_SUGGESTIONS) break;
    // Skip forbidden tactics (compared case-insensitively)
    if (forbidden.has(rule.tactic.toLowerCase())) continue;
    // Skip duplicate tactic names (e.g., both left and right rules match disjunctions)
    if (seen.has(rule.tactic)) continue;

    if (rule.match(goal)) {
      seen.add(rule.tactic);
      suggestions.push({
        tactic: rule.tactic,
        reason: rule.reason,
        confidence: rule.confidence,
        // Link to the full documentation entry from tactic-docs.ts
        doc: tacticDocMap.get(rule.tactic) ?? null,
      });
    }
  }

  return suggestions;
}
