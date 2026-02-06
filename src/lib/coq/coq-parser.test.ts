import { describe, it, expect } from 'vitest';
import { parseStatements, isProofStart, ppToString, stripPpTags, parseGoalData } from './coq-parser';

describe('parseStatements', () => {
  it('splits a basic multi-statement program into individual sentences', () => {
    const code = 'Theorem foo : True. Proof. exact I. Qed.';
    expect(parseStatements(code)).toEqual([
      'Theorem foo : True.',
      'Proof.',
      'exact I.',
      'Qed.',
    ]);
  });

  it('does not split on dots in qualified names like Nat.compare', () => {
    const code = 'Check Nat.compare.';
    expect(parseStatements(code)).toEqual(['Check Nat.compare.']);
  });

  it('does not split on a dot inside a string literal', () => {
    const code = 'Definition x := "hello.". Definition y := 1.';
    expect(parseStatements(code)).toEqual([
      'Definition x := "hello.".',
      'Definition y := 1.',
    ]);
  });

  it('does not split on a dot inside a comment', () => {
    const code = '(* foo. *) Definition x := 1.';
    expect(parseStatements(code)).toEqual([
      '(* foo. *) Definition x := 1.',
    ]);
  });

  it('handles nested comments and preserves depth correctly', () => {
    const code = '(* (* inner. *) outer *) Definition x := 1.';
    expect(parseStatements(code)).toEqual([
      '(* (* inner. *) outer *) Definition x := 1.',
    ]);
  });

  it('handles Coq double-quote escape inside strings', () => {
    const code = 'Definition x := "say ""hello"" world.". Check x.';
    expect(parseStatements(code)).toEqual([
      'Definition x := "say ""hello"" world.".',
      'Check x.',
    ]);
  });

  it('splits on a dot at EOF with no trailing whitespace', () => {
    const code = 'Qed.';
    expect(parseStatements(code)).toEqual(['Qed.']);
  });

  it('returns an empty array for whitespace-only input', () => {
    expect(parseStatements('   \n\t  ')).toEqual([]);
  });

  it('returns an empty array for an empty string', () => {
    expect(parseStatements('')).toEqual([]);
  });

  it('handles a single statement with no trailing space', () => {
    const code = 'Qed.';
    expect(parseStatements(code)).toEqual(['Qed.']);
  });

  it('handles multiple whitespace characters between statements', () => {
    const code = 'Proof.   \n\n\t  exact I.     Qed.';
    expect(parseStatements(code)).toEqual([
      'Proof.',
      'exact I.',
      'Qed.',
    ]);
  });

  it('treats a comment containing a dot as part of the surrounding statement', () => {
    const code = 'Theorem foo (* bar. *) : True.';
    expect(parseStatements(code)).toEqual([
      'Theorem foo (* bar. *) : True.',
    ]);
  });

  it('returns an empty array when input is only a comment with no period-terminated statement', () => {
    const code = '(* just a comment *)';
    expect(parseStatements(code)).toEqual([]);
  });

  it('handles multiple qualified names in a single statement', () => {
    const code = 'Check (Nat.add (List.length l)).';
    expect(parseStatements(code)).toEqual([
      'Check (Nat.add (List.length l)).',
    ]);
  });

  it('handles a statement ending with a dot followed by a newline', () => {
    const code = 'Proof.\nexact I.\nQed.\n';
    expect(parseStatements(code)).toEqual([
      'Proof.',
      'exact I.',
      'Qed.',
    ]);
  });

  it('does not produce empty statements from trailing whitespace after the last dot', () => {
    const code = 'Qed.   ';
    expect(parseStatements(code)).toEqual(['Qed.']);
  });

  it('handles code with no terminating dots as producing no statements', () => {
    const code = 'Definition x := 1';
    expect(parseStatements(code)).toEqual([]);
  });
});

describe('isProofStart', () => {
  it('returns true for "Proof."', () => {
    expect(isProofStart('Proof.')).toBe(true);
  });

  it('returns true for "Proof with auto."', () => {
    expect(isProofStart('Proof with auto.')).toBe(true);
  });

  it('returns true with leading whitespace', () => {
    expect(isProofStart('  Proof.')).toBe(true);
  });

  it('returns false for lowercase "proof." (case-sensitive, Coq requires "Proof")', () => {
    expect(isProofStart('proof.')).toBe(false);
  });

  it('returns false when Proof is inside a comment', () => {
    expect(isProofStart('(* Proof. *)')).toBe(false);
  });

  it('returns false for "Theorem"', () => {
    expect(isProofStart('Theorem')).toBe(false);
  });

  it('returns false for an empty string', () => {
    expect(isProofStart('')).toBe(false);
  });

  it('returns false for "ProofIrrelevance" due to word boundary', () => {
    expect(isProofStart('ProofIrrelevance')).toBe(false);
  });

  it('returns false when Proof appears inside a string literal', () => {
    expect(isProofStart('"Proof"')).toBe(false);
  });

  it('returns false for "PROOF." (case-sensitive, Coq requires "Proof")', () => {
    expect(isProofStart('PROOF.')).toBe(false);
  });

  it('returns false for text before Proof keyword', () => {
    expect(isProofStart('Theorem foo. Proof.')).toBe(false);
  });
});

// ---------------------------------------------------------------------------
// ppToString
// ---------------------------------------------------------------------------

describe('ppToString', () => {
  it('returns a plain string unchanged', () => {
    expect(ppToString('nat')).toBe('nat');
  });

  it('extracts text from Pp_string node', () => {
    expect(ppToString(['Pp_string', 'True'])).toBe('True');
  });

  it('returns empty string for Pp_string with no content', () => {
    expect(ppToString(['Pp_string'])).toBe('');
  });

  it('concatenates children of Pp_glue', () => {
    expect(ppToString(['Pp_glue', [['Pp_string', 'A'], ['Pp_string', ' /\\ '], ['Pp_string', 'B']]])).toBe('A /\\ B');
  });

  it('concatenates children of Pp_box', () => {
    expect(ppToString(['Pp_box', [['Pp_string', 'nat']]])).toBe('nat');
  });

  it('unwraps Pp_tag to its content', () => {
    expect(ppToString(['Pp_tag', 'some_tag', ['Pp_string', 'hello']])).toBe('hello');
  });

  it('converts Pp_force_newline to a space', () => {
    expect(ppToString(['Pp_force_newline'])).toBe(' ');
  });

  it('converts Pp_print_break to a space', () => {
    expect(ppToString(['Pp_print_break'])).toBe(' ');
  });

  it('handles deeply nested Pp AST', () => {
    const ast = ['Pp_glue', [
      ['Pp_tag', 'keyword', ['Pp_string', 'forall']],
      ['Pp_string', ' '],
      ['Pp_box', [['Pp_string', 'A'], ['Pp_string', ' '], ['Pp_string', 'B']]],
      ['Pp_string', ', '],
      ['Pp_glue', [['Pp_string', 'A'], ['Pp_string', ' -> '], ['Pp_string', 'B']]],
    ]];
    expect(ppToString(ast)).toBe('forall A B, A -> B');
  });

  it('converts non-string, non-array values via String()', () => {
    expect(ppToString(42)).toBe('42');
    expect(ppToString(null)).toBe('null');
  });

  it('handles unknown tags by concatenating remaining elements', () => {
    expect(ppToString(['Pp_unknown', ['Pp_string', 'x']])).toBe('x');
  });
});

// ---------------------------------------------------------------------------
// stripPpTags
// ---------------------------------------------------------------------------

describe('stripPpTags', () => {
  it('strips XML-like Pp tags from a string', () => {
    expect(stripPpTags('<Pp_tag>nat</Pp_tag>')).toBe('nat');
  });

  it('strips nested Pp tags', () => {
    expect(stripPpTags('<Pp_box><Pp_tag>A -> B</Pp_tag></Pp_box>')).toBe('A -> B');
  });

  it('strips generic HTML-like tags', () => {
    expect(stripPpTags('<constr_type>Prop</constr_type>')).toBe('Prop');
  });

  it('returns a plain string unchanged', () => {
    expect(stripPpTags('nat')).toBe('nat');
  });

  it('delegates arrays to ppToString', () => {
    expect(stripPpTags(['Pp_string', 'hello'])).toBe('hello');
  });

  it('converts non-string non-array values via String()', () => {
    expect(stripPpTags(undefined)).toBe('undefined');
    expect(stripPpTags(null)).toBe('null');
    expect(stripPpTags(123)).toBe('123');
  });

  it('trims whitespace', () => {
    expect(stripPpTags('  nat  ')).toBe('nat');
  });
});

// ---------------------------------------------------------------------------
// parseGoalData
// ---------------------------------------------------------------------------

describe('parseGoalData', () => {
  it('returns empty array for null/undefined input', () => {
    expect(parseGoalData(null)).toEqual([]);
    expect(parseGoalData(undefined)).toEqual([]);
  });

  it('returns empty array when goalData has no goals field', () => {
    expect(parseGoalData({})).toEqual([]);
    expect(parseGoalData({ stack: [] })).toEqual([]);
  });

  it('returns empty array for empty goals list', () => {
    expect(parseGoalData({ goals: [] })).toEqual([]);
  });

  it('parses a single goal with no hypotheses', () => {
    const data = {
      goals: [{ hyp: [], ty: 'True' }],
    };
    expect(parseGoalData(data)).toEqual([
      { id: 1, hypotheses: [], conclusion: 'True' },
    ]);
  });

  it('parses 3-element hypothesis tuples [names, definition, type] correctly', () => {
    const data = {
      goals: [{
        hyp: [
          [['A'], null, 'Prop'],
          [['B'], null, 'Prop'],
          [['H'], null, 'A /\\ B'],
        ],
        ty: 'B /\\ A',
      }],
    };
    const result = parseGoalData(data);
    expect(result).toHaveLength(1);
    expect(result[0].hypotheses).toEqual([
      { name: 'A', type: 'Prop' },
      { name: 'B', type: 'Prop' },
      { name: 'H', type: 'A /\\ B' },
    ]);
    expect(result[0].conclusion).toBe('B /\\ A');
  });

  it('does not confuse definition (index 1) with type (index 2)', () => {
    // Regular hypothesis: definition is null, type is at index 2
    const data = {
      goals: [{
        hyp: [[['n'], null, 'nat']],
        ty: 'n = n',
      }],
    };
    const result = parseGoalData(data);
    expect(result[0].hypotheses[0].type).toBe('nat');
  });

  it('uses definition as fallback type when only 2-element tuple', () => {
    // Edge case: 2-element tuple [names, type]
    const data = {
      goals: [{
        hyp: [[['x'], 'bool']],
        ty: 'True',
      }],
    };
    const result = parseGoalData(data);
    expect(result[0].hypotheses[0].type).toBe('bool');
  });

  it('handles let-binding hypotheses with non-null definition', () => {
    // let x := 5 : nat  →  [["x"], "5", "nat"]
    const data = {
      goals: [{
        hyp: [[['x'], '5', 'nat']],
        ty: 'x = 5',
      }],
    };
    const result = parseGoalData(data);
    expect(result[0].hypotheses[0].name).toBe('x');
    expect(result[0].hypotheses[0].type).toBe('nat');
  });

  it('joins multiple names in a hypothesis', () => {
    const data = {
      goals: [{
        hyp: [[['a', 'b', 'c'], null, 'nat']],
        ty: 'True',
      }],
    };
    const result = parseGoalData(data);
    expect(result[0].hypotheses[0].name).toBe('a, b, c');
  });

  it('wraps a single non-array name into an array', () => {
    const data = {
      goals: [{
        hyp: [['x', null, 'nat']],
        ty: 'True',
      }],
    };
    const result = parseGoalData(data);
    expect(result[0].hypotheses[0].name).toBe('x');
    expect(result[0].hypotheses[0].type).toBe('nat');
  });

  it('strips Pp AST from hypothesis types and conclusions', () => {
    const data = {
      goals: [{
        hyp: [[['H'], null, ['Pp_string', 'A /\\ B']]],
        ty: ['Pp_glue', [['Pp_string', 'B'], ['Pp_string', ' /\\ '], ['Pp_string', 'A']]],
      }],
    };
    const result = parseGoalData(data);
    expect(result[0].hypotheses[0].type).toBe('A /\\ B');
    expect(result[0].conclusion).toBe('B /\\ A');
  });

  it('parses multiple goals with sequential IDs', () => {
    const data = {
      goals: [
        { hyp: [], ty: 'A' },
        { hyp: [], ty: 'B' },
        { hyp: [], ty: 'C' },
      ],
    };
    const result = parseGoalData(data);
    expect(result).toHaveLength(3);
    expect(result[0]).toEqual({ id: 1, hypotheses: [], conclusion: 'A' });
    expect(result[1]).toEqual({ id: 2, hypotheses: [], conclusion: 'B' });
    expect(result[2]).toEqual({ id: 3, hypotheses: [], conclusion: 'C' });
  });

  it('handles missing hyp field gracefully', () => {
    const data = {
      goals: [{ ty: 'True' }],
    };
    const result = parseGoalData(data);
    expect(result[0].hypotheses).toEqual([]);
    expect(result[0].conclusion).toBe('True');
  });

  it('reads conclusion from "ty" field (jsCoq actual format)', () => {
    const data = {
      goals: [{ hyp: [], ty: 'B /\\ A' }],
    };
    expect(parseGoalData(data)[0].conclusion).toBe('B /\\ A');
  });

  it('falls back to "ccl" when "ty" is absent', () => {
    const data = {
      goals: [{ hyp: [], ccl: 'fallback conclusion' }],
    };
    expect(parseGoalData(data)[0].conclusion).toBe('fallback conclusion');
  });

  it('prefers "ty" over "ccl" when both are present', () => {
    const data = {
      goals: [{ hyp: [], ty: 'from ty', ccl: 'from ccl' }],
    };
    expect(parseGoalData(data)[0].conclusion).toBe('from ty');
  });
});
