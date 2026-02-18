import { describe, it, expect } from 'vitest';
import { formatCoqError } from './error-helper';
import type { FormattedError } from './error-helper';

describe('formatCoqError', () => {
  // ── Unification failure ─────────────────────────────────────────────
  it('translates unification failure', () => {
    const result = formatCoqError('Unable to unify "nat" with "bool"');
    expect(result.friendly).not.toBeNull();
    expect(result.friendly).toContain('nat');
    expect(result.friendly).toContain('bool');
    expect(result.raw).toBe('Unable to unify "nat" with "bool"');
  });

  // ── No more subgoals ───────────────────────────────────────────────
  it('translates "No more subgoals"', () => {
    const result = formatCoqError('No more subgoals');
    expect(result.friendly).toContain('already complete');
  });

  // ── Not a proposition ──────────────────────────────────────────────
  it('translates "Not a proposition or a type"', () => {
    const result = formatCoqError('Not a proposition or a type');
    expect(result.friendly).toContain('proposition');
  });

  // ── Variable not found ─────────────────────────────────────────────
  it('translates "The variable X was not found"', () => {
    const result = formatCoqError('The variable H was not found in the current environment');
    expect(result.friendly).toContain('"H"');
    expect(result.friendly).toContain('intros');
  });

  // ── Instance not found ─────────────────────────────────────────────
  it('translates "Unable to find an instance"', () => {
    const result = formatCoqError('Unable to find an instance for...');
    expect(result.friendly).toContain('explicitly');
  });

  // ── Type mismatch with term info ───────────────────────────────────
  it('translates detailed type mismatch', () => {
    const result = formatCoqError(
      'The term "0" has type "nat" while it is expected to have type "bool"'
    );
    expect(result.friendly).toContain('"0"');
    expect(result.friendly).toContain('"nat"');
    expect(result.friendly).toContain('"bool"');
  });

  // ── Environment type error ─────────────────────────────────────────
  it('translates environment type error', () => {
    const result = formatCoqError('In environment\nn : nat\nThe term "n" has type "nat"');
    expect(result.friendly).toContain('Type error');
  });

  // ── No such goal ───────────────────────────────────────────────────
  it('translates "No such goal"', () => {
    const result = formatCoqError('No such goal');
    expect(result.friendly).toContain('no goal');
  });

  // ── Syntax error ───────────────────────────────────────────────────
  it('translates "Syntax error"', () => {
    const result = formatCoqError('Syntax error: unexpected token');
    expect(result.friendly).toContain('Syntax error');
  });

  // ── Reference not found ────────────────────────────────────────────
  it('translates "The reference X was not found"', () => {
    const result = formatCoqError('The reference foo was not found in the current environment');
    expect(result.friendly).toContain('"foo"');
    expect(result.friendly).toContain('spelling');
  });

  // ── No matching clauses ────────────────────────────────────────────
  it('translates "No matching clauses for match"', () => {
    const result = formatCoqError('No matching clauses for match');
    expect(result.friendly).toContain('incomplete');
  });

  // ── Cannot find physical path ──────────────────────────────────────
  it('translates "Cannot find a physical path"', () => {
    const result = formatCoqError('Cannot find a physical path bound to...');
    expect(result.friendly).toContain('library');
  });

  // ── Tactic failure ─────────────────────────────────────────────────
  it('translates "Tactic failure"', () => {
    const result = formatCoqError('Tactic failure: cannot unify');
    expect(result.friendly).toContain('tactic failed');
  });

  // ── Unknown error returns null friendly ────────────────────────────
  it('returns null friendly for unknown errors', () => {
    const result = formatCoqError('Some completely unknown error XYZ');
    expect(result.raw).toBe('Some completely unknown error XYZ');
    expect(result.friendly).toBeNull();
  });

  // ── Empty string ───────────────────────────────────────────────────
  it('returns null friendly for empty string', () => {
    const result = formatCoqError('');
    expect(result.raw).toBe('');
    expect(result.friendly).toBeNull();
  });

  // ── Always preserves raw ───────────────────────────────────────────
  it('always preserves the raw error string', () => {
    const errors = [
      'Unable to unify "A" with "B"',
      'No more subgoals',
      'Unknown random error',
    ];
    for (const err of errors) {
      expect(formatCoqError(err).raw).toBe(err);
    }
  });

  // ── Pattern priority: specific before general ──────────────────────
  it('matches specific unification pattern before generic environment pattern', () => {
    const result = formatCoqError('Unable to unify "nat" with "bool"');
    // Should match the specific "Unable to unify" pattern, not fall through
    expect(result.friendly).toContain('Type mismatch');
  });

  it('matches detailed type mismatch before environment pattern', () => {
    // This error contains "The term" which the environment pattern also matches,
    // but the specific pattern should win
    const result = formatCoqError(
      'The term "x" has type "nat" while it is expected to have type "bool"'
    );
    expect(result.friendly).toContain('Wrong type');
  });

  // ── Return type shape ──────────────────────────────────────────────
  it('returns a FormattedError object', () => {
    const result: FormattedError = formatCoqError('test');
    expect(result).toHaveProperty('raw');
    expect(result).toHaveProperty('friendly');
  });
});
