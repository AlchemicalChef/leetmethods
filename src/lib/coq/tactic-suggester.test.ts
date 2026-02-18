import { describe, it, expect } from 'vitest';
import { suggestTactics } from './tactic-suggester';
import type { CoqGoal } from './types';

const goal = (conclusion: string, hypotheses: Array<{ name: string; type: string }> = []): CoqGoal => ({
  id: 1,
  hypotheses,
  conclusion,
});

const hyp = (name: string, type: string) => ({ name, type });

describe('suggestTactics', () => {
  // ── Empty goals ──────────────────────────────────────────────────────
  it('returns empty array when goals is empty', () => {
    expect(suggestTactics({ goals: [] })).toEqual([]);
  });

  // ── High confidence ──────────────────────────────────────────────────
  describe('high confidence', () => {
    it('suggests split for conjunction /\\', () => {
      const result = suggestTactics({ goals: [goal('P /\\ Q')] });
      expect(result.some(s => s.tactic === 'split' && s.confidence === 'high')).toBe(true);
    });

    it('suggests split for Unicode conjunction', () => {
      const result = suggestTactics({ goals: [goal('P \u2227 Q')] });
      expect(result.some(s => s.tactic === 'split' && s.confidence === 'high')).toBe(true);
    });

    it('suggests left and right for disjunction \\/', () => {
      const result = suggestTactics({ goals: [goal('P \\/ Q')] });
      expect(result.some(s => s.tactic === 'left' && s.confidence === 'high')).toBe(true);
      expect(result.some(s => s.tactic === 'right' && s.confidence === 'high')).toBe(true);
    });

    it('suggests intros for implication ->', () => {
      const result = suggestTactics({ goals: [goal('P -> Q')] });
      expect(result.some(s => s.tactic === 'intros' && s.confidence === 'high')).toBe(true);
    });

    it('suggests intros for forall', () => {
      const result = suggestTactics({ goals: [goal('forall n : nat, n = n')] });
      expect(result.some(s => s.tactic === 'intros' && s.confidence === 'high')).toBe(true);
    });

    it('suggests exists for existential', () => {
      const result = suggestTactics({ goals: [goal('exists n : nat, n = 0')] });
      expect(result.some(s => s.tactic === 'exists' && s.confidence === 'high')).toBe(true);
    });

    it('suggests reflexivity for identical equality sides', () => {
      const result = suggestTactics({ goals: [goal('n = n')] });
      expect(result.some(s => s.tactic === 'reflexivity' && s.confidence === 'high')).toBe(true);
    });

    it('does not suggest reflexivity when sides differ', () => {
      const result = suggestTactics({ goals: [goal('n = m')] });
      expect(result.some(s => s.tactic === 'reflexivity')).toBe(false);
    });

    it('suggests exact I for conclusion True', () => {
      const result = suggestTactics({ goals: [goal('True')] });
      expect(result.some(s => s.tactic === 'exact I' && s.confidence === 'high')).toBe(true);
    });

    it('suggests contradiction for False hypothesis', () => {
      const result = suggestTactics({ goals: [goal('P', [hyp('H', 'False')])] });
      expect(result.some(s => s.tactic === 'contradiction' && s.confidence === 'high')).toBe(true);
    });

    it('suggests f_equal for S constructor S n = S m', () => {
      const result = suggestTactics({ goals: [goal('S n = S m')] });
      expect(result.some(s => s.tactic === 'f_equal' && s.confidence === 'high')).toBe(true);
    });

    it('does not suggest f_equal when S sides are identical', () => {
      const result = suggestTactics({ goals: [goal('S n = S n')] });
      expect(result.some(s => s.tactic === 'f_equal')).toBe(false);
    });
  });

  // ── Medium confidence ────────────────────────────────────────────────
  describe('medium confidence', () => {
    it('suggests rewrite for hypothesis with equality', () => {
      const result = suggestTactics({ goals: [goal('Q', [hyp('H', 'x = y')])] });
      expect(result.some(s => s.tactic === 'rewrite' && s.confidence === 'medium')).toBe(true);
    });

    it('suggests assumption when hypothesis type matches conclusion', () => {
      const result = suggestTactics({ goals: [goal('P', [hyp('H', 'P')])] });
      expect(result.some(s => s.tactic === 'assumption' && s.confidence === 'medium')).toBe(true);
    });

    it('suggests apply when hypothesis implication concludes at goal', () => {
      const result = suggestTactics({ goals: [goal('Q', [hyp('H', 'P -> Q')])] });
      expect(result.some(s => s.tactic === 'apply' && s.confidence === 'medium')).toBe(true);
    });

    it('suggests induction for goal involving nat', () => {
      const result = suggestTactics({ goals: [goal('forall n : nat, P n')] });
      expect(result.some(s => s.tactic === 'induction' && s.confidence === 'medium')).toBe(true);
    });

    it('deduplicates induction for nat+list goals', () => {
      const result = suggestTactics({ goals: [goal('forall (n : nat) (l : list A), P n l')] });
      const inductionSuggestions = result.filter(s => s.tactic === 'induction');
      expect(inductionSuggestions).toHaveLength(1);
    });
  });

  // ── Low confidence ───────────────────────────────────────────────────
  describe('low confidence', () => {
    it('suggests simpl and auto when no high/medium rules match', () => {
      const result = suggestTactics({ goals: [goal('some_custom_prop')] });
      expect(result.some(s => s.tactic === 'simpl' && s.confidence === 'low')).toBe(true);
      expect(result.some(s => s.tactic === 'auto' && s.confidence === 'low')).toBe(true);
    });
  });

  // ── Max suggestions ──────────────────────────────────────────────────
  it('never returns more than 3 suggestions', () => {
    const result = suggestTactics({
      goals: [goal('P /\\ Q -> R \\/ S', [hyp('H1', 'x = y'), hyp('H2', 'False')])],
    });
    expect(result.length).toBeLessThanOrEqual(3);
  });

  // ── Forbidden tactics ────────────────────────────────────────────────
  describe('forbidden tactics', () => {
    it('excludes forbidden tactics case-insensitively', () => {
      const result = suggestTactics({
        goals: [goal('P /\\ Q')],
        forbiddenTactics: ['SPLIT'],
      });
      expect(result.some(s => s.tactic === 'split')).toBe(false);
    });

    it('excludes multiple forbidden tactics', () => {
      const result = suggestTactics({
        goals: [goal('P -> Q')],
        forbiddenTactics: ['intros', 'simpl'],
      });
      expect(result.some(s => s.tactic === 'intros')).toBe(false);
      expect(result.some(s => s.tactic === 'simpl')).toBe(false);
    });
  });

  // ── Priority ordering ────────────────────────────────────────────────
  it('returns high confidence suggestions before medium and low', () => {
    const result = suggestTactics({
      goals: [goal('P /\\ Q', [hyp('H', 'x = y')])],
    });
    const confidences = result.map(s => s.confidence);
    const order = { high: 0, medium: 1, low: 2 };
    for (let i = 0; i < confidences.length - 1; i++) {
      expect(order[confidences[i]]).toBeLessThanOrEqual(order[confidences[i + 1]]);
    }
  });

  // ── No duplicates ────────────────────────────────────────────────────
  it('does not return duplicate tactic names', () => {
    const result = suggestTactics({
      goals: [goal('P /\\ Q \\/ R -> S', [hyp('H', 'x = y')])],
    });
    const names = result.map(s => s.tactic);
    expect(names.length).toBe(new Set(names).size);
  });

  // ── Doc property ─────────────────────────────────────────────────────
  it('suggestions for known tactics have non-null doc', () => {
    const result = suggestTactics({ goals: [goal('P /\\ Q')] });
    const splitSuggestion = result.find(s => s.tactic === 'split');
    expect(splitSuggestion?.doc).not.toBeNull();
  });

  it('all suggestions have doc property defined', () => {
    const result = suggestTactics({ goals: [goal('P -> Q')] });
    result.forEach(s => {
      expect(s).toHaveProperty('doc');
    });
  });

  // ── Reason field ─────────────────────────────────────────────────────
  it('all suggestions have a non-empty reason', () => {
    const result = suggestTactics({ goals: [goal('P /\\ Q')] });
    result.forEach(s => {
      expect(typeof s.reason).toBe('string');
      expect(s.reason.length).toBeGreaterThan(0);
    });
  });
});
