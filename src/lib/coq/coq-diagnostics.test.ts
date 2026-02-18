import { describe, it, expect } from 'vitest';
import { computeErrorDiagnostic } from './coq-diagnostics';

describe('computeErrorDiagnostic', () => {
  // Helper: build "prelude\n\nuserCode"
  const full = (prelude: string, userCode: string) => prelude + '\n\n' + userCode;

  it('returns null for negative failingIndex', () => {
    const result = computeErrorDiagnostic('intros.', -1, 0, 'error');
    expect(result).toBeNull();
  });

  it('returns null for failingIndex beyond statement count', () => {
    const code = full('', 'intros.');
    // Only 1 statement at index 0
    const result = computeErrorDiagnostic(code, 1, 0, 'error');
    expect(result).toBeNull();
  });

  it('returns null when the failing statement is inside the prelude', () => {
    const prelude = 'Require Import Nat.';
    const code = full(prelude, 'intros.');
    // failingIndex 0 = "Require Import Nat." which is in the prelude
    const result = computeErrorDiagnostic(code, 0, prelude.length, 'error');
    expect(result).toBeNull();
  });

  it('locates the first user-code statement (no prelude)', () => {
    const code = full('', 'intros.');
    const result = computeErrorDiagnostic(code, 0, 0, 'some error');
    expect(result).not.toBeNull();
    expect(result!.from).toBe(0);
    expect(result!.to).toBe('intros.'.length);
    expect(result!.message).toBe('some error');
    expect(result!.severity).toBe('error');
  });

  it('subtracts prelude offset correctly', () => {
    const prelude = 'Require Import Nat.';
    const userCode = 'intros. apply H.';
    const code = full(prelude, userCode);
    // Statements: ["Require Import Nat.", "intros.", "apply H."]
    // failingIndex 2 = "apply H." (the second user-code statement)
    const result = computeErrorDiagnostic(code, 2, prelude.length, 'error');
    expect(result).not.toBeNull();
    // "apply H." starts at position 7 in userCode ("intros. " is 8 chars, but
    // "intros." is 7 chars + the space before "apply")
    expect(result!.from).toBe('intros. '.length);
    expect(result!.to).toBe('intros. apply H.'.length);
  });

  it('handles multiple prelude statements', () => {
    const prelude = 'Require Import Nat. Require Import Lia.';
    const userCode = 'intros.';
    const code = full(prelude, userCode);
    // Statements: ["Require Import Nat.", "Require Import Lia.", "intros."]
    const result = computeErrorDiagnostic(code, 2, prelude.length, 'err');
    expect(result).not.toBeNull();
    expect(result!.from).toBe(0);
    expect(result!.to).toBe('intros.'.length);
  });

  it('includes comment prefix in diagnostic range (parseStatements keeps comments in statement)', () => {
    const code = full('', 'intros. (* a comment *) apply H.');
    // parseStatements returns: ["intros.", "(* a comment *) apply H."]
    // The second statement includes the comment, so the diagnostic covers it
    const result = computeErrorDiagnostic(code, 1, 0, 'error');
    expect(result).not.toBeNull();
    expect(result!.from).toBe('intros. '.length);
    expect(result!.to).toBe('intros. (* a comment *) apply H.'.length);
  });

  it('handles single statement error at index 0 with prelude', () => {
    const prelude = 'Import X.';
    const userCode = 'reflexivity.';
    const code = full(prelude, userCode);
    // Statements: ["Import X.", "reflexivity."]
    const result = computeErrorDiagnostic(code, 1, prelude.length, 'no match');
    expect(result).not.toBeNull();
    expect(result!.from).toBe(0);
    expect(result!.to).toBe('reflexivity.'.length);
    expect(result!.message).toBe('no match');
  });

  it('clamps from to 0 when statement overlaps prelude boundary', () => {
    // Edge case: prelude is empty string, separator is "\n\n"
    const code = '\n\nintros.';
    const result = computeErrorDiagnostic(code, 0, 0, 'err');
    expect(result).not.toBeNull();
    expect(result!.from).toBe(0);
  });
});
