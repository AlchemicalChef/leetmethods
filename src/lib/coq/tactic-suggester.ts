import type { CoqGoal } from './types';
import { tacticDocMap } from './tactic-docs';
import type { TacticDoc } from './tactic-docs';

export type Confidence = 'high' | 'medium' | 'low';

export interface TacticSuggestion {
  tactic: string;
  reason: string;
  confidence: Confidence;
  doc: TacticDoc | null;
}

interface SuggestionContext {
  goals: CoqGoal[];
  forbiddenTactics?: string[];
}

const MAX_SUGGESTIONS = 3;

interface Rule {
  confidence: Confidence;
  match: (goal: CoqGoal) => boolean;
  tactic: string;
  reason: string;
}

const highConfidenceRules: Rule[] = [
  {
    confidence: 'high',
    match: (g) => g.conclusion.includes('/\\') || g.conclusion.includes('∧'),
    tactic: 'split',
    reason: 'Your goal is a conjunction - use split to break it into two subgoals',
  },
  {
    confidence: 'high',
    match: (g) => g.conclusion.includes('\\/') || g.conclusion.includes('∨'),
    tactic: 'left',
    reason: 'Your goal is a disjunction - use left or right to pick a side',
  },
  {
    confidence: 'high',
    match: (g) => g.conclusion.startsWith('forall') || g.conclusion.includes('->'),
    tactic: 'intros',
    reason: 'Your goal has a universal quantifier or implication - introduce variables/hypotheses',
  },
  {
    confidence: 'high',
    match: (g) => g.conclusion.startsWith('exists') || g.conclusion.includes('∃'),
    tactic: 'exists',
    reason: 'Your goal is existential - provide a witness with exists',
  },
  {
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
    confidence: 'high',
    match: (g) => g.conclusion.trim() === 'True',
    tactic: 'exact I',
    reason: 'The goal is True - exact I provides the proof directly',
  },
  {
    confidence: 'high',
    match: (g) => g.hypotheses.some((h) => h.type.trim() === 'False'),
    tactic: 'contradiction',
    reason: 'You have False as a hypothesis - contradiction solves any goal',
  },
  {
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

const mediumConfidenceRules: Rule[] = [
  {
    confidence: 'medium',
    match: (g) => g.hypotheses.some((h) => {
      const eqMatch = h.type.match(/^(.+)\s*=\s*(.+)$/);
      return !!eqMatch;
    }),
    tactic: 'rewrite',
    reason: 'You have an equality hypothesis - rewrite can substitute it into the goal',
  },
  {
    confidence: 'medium',
    match: (g) => g.hypotheses.some((h) => h.type.trim() === g.conclusion.trim()),
    tactic: 'assumption',
    reason: 'A hypothesis exactly matches the goal - assumption solves it',
  },
  {
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
    confidence: 'medium',
    match: (g) => g.conclusion.includes('nat') || g.hypotheses.some((h) => h.type.includes('nat')),
    tactic: 'induction',
    reason: 'The goal involves natural numbers - induction is often the right strategy',
  },
  {
    confidence: 'medium',
    match: (g) => g.conclusion.includes('list') || g.hypotheses.some((h) => h.type.includes('list')),
    tactic: 'induction',
    reason: 'The goal involves lists - structural induction is a common approach',
  },
];

const lowConfidenceRules: Rule[] = [
  {
    confidence: 'low',
    match: () => true,
    tactic: 'simpl',
    reason: 'Try simplifying - simpl reduces definitions and computations',
  },
  {
    confidence: 'low',
    match: () => true,
    tactic: 'auto',
    reason: 'Try auto - it combines simple tactics to solve easy goals',
  },
];

export function suggestTactics(context: SuggestionContext): TacticSuggestion[] {
  if (context.goals.length === 0) return [];

  const goal = context.goals[0];
  const forbidden = new Set((context.forbiddenTactics ?? []).map((t) => t.toLowerCase()));
  const seen = new Set<string>();
  const suggestions: TacticSuggestion[] = [];

  const allRules = [...highConfidenceRules, ...mediumConfidenceRules, ...lowConfidenceRules];

  for (const rule of allRules) {
    if (suggestions.length >= MAX_SUGGESTIONS) break;
    if (forbidden.has(rule.tactic.toLowerCase())) continue;
    if (seen.has(rule.tactic)) continue;

    if (rule.match(goal)) {
      seen.add(rule.tactic);
      suggestions.push({
        tactic: rule.tactic,
        reason: rule.reason,
        confidence: rule.confidence,
        doc: tacticDocMap.get(rule.tactic) ?? null,
      });
    }
  }

  return suggestions;
}
