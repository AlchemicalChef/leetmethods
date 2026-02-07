import { describe, it, expect } from 'vitest';
import { checkForbiddenTactics, isProofComplete } from './verifier';

// ---------------------------------------------------------------------------
// checkForbiddenTactics
// ---------------------------------------------------------------------------

describe('checkForbiddenTactics', () => {
  // --- Known forbidden tactic detection ---

  it('detects "admit" in code', () => {
    const result = checkForbiddenTactics('intros. admit.', ['admit']);
    expect(result.hasForbidden).toBe(true);
    expect(result.found).toEqual(['admit']);
  });

  it('detects "Admitted" in code', () => {
    const result = checkForbiddenTactics('Proof. auto. Admitted.', ['Admitted']);
    expect(result.hasForbidden).toBe(true);
    expect(result.found).toEqual(['Admitted']);
  });

  it('detects "Abort" in code', () => {
    const result = checkForbiddenTactics('Proof. Abort.', ['Abort']);
    expect(result.hasForbidden).toBe(true);
    expect(result.found).toEqual(['Abort']);
  });

  it('detects "Axiom" in code', () => {
    const result = checkForbiddenTactics('Axiom classic : forall P, P.', ['Axiom']);
    expect(result.hasForbidden).toBe(true);
    expect(result.found).toEqual(['Axiom']);
  });

  it('detects "Parameter" in code', () => {
    const result = checkForbiddenTactics('Parameter x : nat.', ['Parameter']);
    expect(result.hasForbidden).toBe(true);
    expect(result.found).toEqual(['Parameter']);
  });

  it('detects "Conjecture" in code', () => {
    const result = checkForbiddenTactics('Conjecture c : True.', ['Conjecture']);
    expect(result.hasForbidden).toBe(true);
    expect(result.found).toEqual(['Conjecture']);
  });

  // --- Case sensitivity ---

  it('"admit" pattern is case-sensitive (matches lowercase "admit")', () => {
    const result = checkForbiddenTactics('intros. admit.', ['admit']);
    expect(result.hasForbidden).toBe(true);
    expect(result.found).toEqual(['admit']);
  });

  it('"admit" pattern is case-sensitive (does not match "Admit" or "ADMIT")', () => {
    expect(checkForbiddenTactics('intros. Admit.', ['admit']).hasForbidden).toBe(false);
    expect(checkForbiddenTactics('intros. ADMIT.', ['admit']).hasForbidden).toBe(false);
  });

  it('"Admitted" pattern is case-sensitive (does not match "admitted")', () => {
    const result = checkForbiddenTactics('admitted.', ['Admitted']);
    expect(result.hasForbidden).toBe(false);
    expect(result.found).toEqual([]);
  });

  it('"Abort" pattern is case-sensitive (does not match "abort")', () => {
    const result = checkForbiddenTactics('abort.', ['Abort']);
    expect(result.hasForbidden).toBe(false);
    expect(result.found).toEqual([]);
  });

  // --- Dynamic regex for unknown tactic names ---

  it('creates a dynamic regex for an unknown tactic name', () => {
    const result = checkForbiddenTactics('intros. tauto.', ['tauto']);
    expect(result.hasForbidden).toBe(true);
    expect(result.found).toEqual(['tauto']);
  });

  it('dynamic regex respects word boundaries', () => {
    // "tauto" should not match inside "tautomatic" (not a real word, but tests boundary)
    const result = checkForbiddenTactics('intros. tautomatic.', ['tauto']);
    expect(result.hasForbidden).toBe(false);
    expect(result.found).toEqual([]);
  });

  it('dynamic regex escapes special characters in tactic names', () => {
    // A contrived tactic name with regex-special chars
    const result = checkForbiddenTactics('foo. bar+baz. qux.', ['bar+baz']);
    expect(result.hasForbidden).toBe(true);
    expect(result.found).toEqual(['bar+baz']);
  });

  // --- Comment stripping (indirect test of stripCoqComments) ---

  it('ignores forbidden tactics inside a single-line comment', () => {
    const result = checkForbiddenTactics('intros. (* admit *) reflexivity.', ['admit']);
    expect(result.hasForbidden).toBe(false);
    expect(result.found).toEqual([]);
  });

  it('ignores forbidden tactics inside a multi-line comment', () => {
    const code = `intros.
(* This is a long comment
   that contains Admitted and Abort
*)
reflexivity.`;
    const result = checkForbiddenTactics(code, ['Admitted', 'Abort']);
    expect(result.hasForbidden).toBe(false);
    expect(result.found).toEqual([]);
  });

  it('ignores forbidden tactics inside nested comments', () => {
    const code = 'intros. (* outer (* admit *) still comment *) reflexivity.';
    const result = checkForbiddenTactics(code, ['admit']);
    expect(result.hasForbidden).toBe(false);
    expect(result.found).toEqual([]);
  });

  it('detects forbidden tactics outside comments when comment also present', () => {
    const code = '(* safe comment *) admit.';
    const result = checkForbiddenTactics(code, ['admit']);
    expect(result.hasForbidden).toBe(true);
    expect(result.found).toEqual(['admit']);
  });

  // --- Empty and clean code ---

  it('returns no findings when forbidden list is empty', () => {
    const result = checkForbiddenTactics('admit. Admitted. Abort.', []);
    expect(result.hasForbidden).toBe(false);
    expect(result.found).toEqual([]);
  });

  it('returns no findings when code has no forbidden tactics', () => {
    const result = checkForbiddenTactics('intros. reflexivity. Qed.', ['admit', 'Admitted']);
    expect(result.hasForbidden).toBe(false);
    expect(result.found).toEqual([]);
  });

  it('returns no findings for empty code', () => {
    const result = checkForbiddenTactics('', ['admit', 'Admitted']);
    expect(result.hasForbidden).toBe(false);
    expect(result.found).toEqual([]);
  });

  // --- Multiple findings ---

  it('reports multiple forbidden tactics found at once', () => {
    const code = 'admit. Admitted. Abort.';
    const result = checkForbiddenTactics(code, ['admit', 'Admitted', 'Abort']);
    expect(result.hasForbidden).toBe(true);
    expect(result.found).toEqual(['admit', 'Admitted', 'Abort']);
  });

  it('only reports tactics that are actually present', () => {
    const code = 'admit. reflexivity.';
    const result = checkForbiddenTactics(code, ['admit', 'Admitted', 'Abort']);
    expect(result.hasForbidden).toBe(true);
    expect(result.found).toEqual(['admit']);
  });
});

// ---------------------------------------------------------------------------
// isProofComplete
// ---------------------------------------------------------------------------

describe('isProofComplete', () => {
  it('returns true for code ending with "Qed."', () => {
    expect(isProofComplete('Proof. intros. reflexivity. Qed.')).toBe(true);
  });

  it('returns true for code ending with "Defined."', () => {
    expect(isProofComplete('Proof. exact 42. Defined.')).toBe(true);
  });

  it('returns true with trailing whitespace after "Qed."', () => {
    expect(isProofComplete('Proof. auto. Qed.   ')).toBe(true);
  });

  it('returns true with trailing newline after "Qed."', () => {
    expect(isProofComplete('Proof. auto. Qed.\n')).toBe(true);
  });

  it('returns true with whitespace between Qed and period', () => {
    expect(isProofComplete('Proof. auto. Qed .')).toBe(true);
  });

  it('returns false for "Qed" without a period', () => {
    expect(isProofComplete('Proof. auto. Qed')).toBe(false);
  });

  it('returns false for "Qed." inside a comment', () => {
    expect(isProofComplete('Proof. auto. (* Qed. *)')).toBe(false);
  });

  it('returns false for code without any terminator', () => {
    expect(isProofComplete('Proof. intros. reflexivity.')).toBe(false);
  });

  it('returns true for "Qed." on any line due to multiline regex', () => {
    // The regex uses /m flag, so Qed. at end of any line matches
    expect(isProofComplete('Qed.\nintros. reflexivity.')).toBe(true);
  });

  it('returns false when "Qed" appears mid-line without proper termination', () => {
    expect(isProofComplete('foo Qed bar')).toBe(false);
  });

  it('returns false for empty string', () => {
    expect(isProofComplete('')).toBe(false);
  });

  it('returns false for code that is only a comment', () => {
    expect(isProofComplete('(* Qed. *)')).toBe(false);
  });

  it('returns false for "Admitted." (not a valid terminator)', () => {
    expect(isProofComplete('Proof. auto. Admitted.')).toBe(false);
  });
});

// ---------------------------------------------------------------------------
// Edge cases (comment stripping exercised through public API)
// ---------------------------------------------------------------------------

describe('edge cases', () => {
  it('handles code that is entirely a comment', () => {
    const code = '(* everything is a comment *)';
    expect(checkForbiddenTactics(code, ['admit']).hasForbidden).toBe(false);
    expect(isProofComplete(code)).toBe(false);
  });

  it('handles nested comments at multiple depths', () => {
    const code = '(* level1 (* level2 (* level3 admit *) *) *) reflexivity. Qed.';
    expect(checkForbiddenTactics(code, ['admit']).hasForbidden).toBe(false);
    expect(isProofComplete(code)).toBe(true);
  });

  it('handles empty string for all functions', () => {
    expect(checkForbiddenTactics('', []).hasForbidden).toBe(false);
    expect(isProofComplete('')).toBe(false);
  });

  it('handles code with no comments and no tactics normally', () => {
    const code = 'intros n. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.';
    expect(checkForbiddenTactics(code, ['admit']).hasForbidden).toBe(false);
    expect(isProofComplete(code)).toBe(true);
  });

  it('handles unclosed comment gracefully (rest of code is swallowed)', () => {
    // An unclosed comment means everything after (* is considered inside the comment
    const code = '(* unclosed comment admit Qed.';
    expect(checkForbiddenTactics(code, ['admit']).hasForbidden).toBe(false);
    expect(isProofComplete(code)).toBe(false);
  });
});
