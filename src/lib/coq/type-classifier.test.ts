import { describe, it, expect } from 'vitest';
import { classifyType, getTypeBadge } from './type-classifier';
import type { TypeKind } from './type-classifier';

describe('classifyType', () => {
  // ── Sort types ──────────────────────────────────────────────────────
  describe('sort', () => {
    it.each(['Prop', 'Type', 'Set', 'SProp'])('classifies "%s" as sort', (type) => {
      expect(classifyType(type)).toBe('sort');
    });

    it('classifies with leading/trailing whitespace', () => {
      expect(classifyType('  Prop  ')).toBe('sort');
    });

    it('does NOT classify "Prop -> Prop" as sort (not exact match)', () => {
      expect(classifyType('Prop -> Prop')).not.toBe('sort');
    });

    it('does NOT classify "Type nat" as sort (has argument)', () => {
      expect(classifyType('Type nat')).not.toBe('sort');
    });
  });

  // ── Dependent types ─────────────────────────────────────────────────
  describe('dependent', () => {
    it('classifies "forall n : nat, n = 0" as dependent', () => {
      expect(classifyType('forall n : nat, n = 0')).toBe('dependent');
    });

    it('classifies "forall P : Prop, P -> P" as dependent', () => {
      expect(classifyType('forall P : Prop, P -> P')).toBe('dependent');
    });

    it('classifies "forall(n : nat), n = n" as dependent (no space)', () => {
      expect(classifyType('forall(n : nat), n = n')).toBe('dependent');
    });

    it('prioritizes dependent over equality', () => {
      // Contains "=" but starts with "forall" — should be dependent
      expect(classifyType('forall n : nat, n = 0 -> P n')).toBe('dependent');
    });
  });

  // ── Equality types ──────────────────────────────────────────────────
  describe('equality', () => {
    it('classifies "n = 0" as equality', () => {
      expect(classifyType('n = 0')).toBe('equality');
    });

    it('classifies "a + b = b + a" as equality', () => {
      expect(classifyType('a + b = b + a')).toBe('equality');
    });

    it('classifies "x =? y = true" as equality', () => {
      expect(classifyType('x =? y = true')).toBe('equality');
    });
  });

  // ── Proposition types ───────────────────────────────────────────────
  describe('proposition', () => {
    it.each(['True', 'False', 'and A B', 'or A B', 'not P', 'iff A B', 'le n m', 'lt n m'])
      ('classifies "%s" as proposition', (type) => {
        expect(classifyType(type)).toBe('proposition');
      });

    it('classifies "~ P" as proposition (negation notation)', () => {
      expect(classifyType('~ P')).toBe('proposition');
    });

    it('classifies "A /\\ B" as proposition (conjunction)', () => {
      expect(classifyType('A /\\ B')).toBe('proposition');
    });

    it('classifies "A \\/ B" as proposition (disjunction)', () => {
      expect(classifyType('A \\/ B')).toBe('proposition');
    });

    it('classifies "A <-> B" as proposition (iff notation)', () => {
      expect(classifyType('A <-> B')).toBe('proposition');
    });
  });

  // ── Inductive types ─────────────────────────────────────────────────
  describe('inductive', () => {
    it.each(['nat', 'bool', 'list nat', 'option nat', 'prod A B', 'Z', 'positive'])
      ('classifies "%s" as inductive', (type) => {
        expect(classifyType(type)).toBe('inductive');
      });
  });

  // ── Function types ──────────────────────────────────────────────────
  describe('function', () => {
    it('classifies "A -> B" as function', () => {
      expect(classifyType('A -> B')).toBe('function');
    });

    it('classifies "A -> B -> C" as function', () => {
      expect(classifyType('A -> B -> C')).toBe('function');
    });

    it('classifies "nat -> nat" as inductive (head "nat" takes priority)', () => {
      // head is "nat" which is a known inductive type — inductive > function
      expect(classifyType('nat -> nat')).toBe('inductive');
    });

    it('does NOT misclassify "<->" as function', () => {
      // "<->" should be proposition, not function
      expect(classifyType('A <-> B')).toBe('proposition');
    });
  });

  // ── Unknown types ───────────────────────────────────────────────────
  describe('unknown', () => {
    it('classifies unknown identifiers as unknown', () => {
      expect(classifyType('MyCustomType')).toBe('unknown');
    });

    it('classifies empty string as unknown', () => {
      expect(classifyType('')).toBe('unknown');
    });
  });

  // ── Priority ordering ──────────────────────────────────────────────
  describe('priority ordering', () => {
    it('sort > dependent: "Prop" is sort not dependent', () => {
      expect(classifyType('Prop')).toBe('sort');
    });

    it('dependent > equality: "forall n, n = 0" is dependent', () => {
      expect(classifyType('forall n, n = 0')).toBe('dependent');
    });

    it('equality > proposition: "eq n m" has "=" pattern but "eq" head is proposition', () => {
      // "eq n m" — head is "eq" which is in PROP_TYPES, but no " = " pattern
      expect(classifyType('eq n m')).toBe('proposition');
    });

    it('proposition > inductive: "True" is proposition not inductive', () => {
      expect(classifyType('True')).toBe('proposition');
    });

    it('proposition > function: "A <-> B" has -> but is proposition', () => {
      expect(classifyType('A <-> B')).toBe('proposition');
    });
  });
});

describe('getTypeBadge', () => {
  it('returns badge info for known types', () => {
    const badge = getTypeBadge('nat');
    expect(badge).not.toBeNull();
    expect(badge!.label).toBe('ind');
    expect(badge!.className).toBeTruthy();
    expect(badge!.title).toBeTruthy();
  });

  it('returns null for unknown types', () => {
    expect(getTypeBadge('MyCustomType')).toBeNull();
  });

  const expectedLabels: [string, TypeKind, string][] = [
    ['nat', 'inductive', 'ind'],
    ['True', 'proposition', 'prop'],
    ['Prop', 'sort', 'sort'],
    ['A -> B', 'function', 'fun'],
    ['forall n, n = n', 'dependent', 'dep'],
    ['n = 0', 'equality', 'eq'],
  ];

  it.each(expectedLabels)('getTypeBadge("%s") returns label "%s"', (type, _kind, label) => {
    const badge = getTypeBadge(type);
    expect(badge).not.toBeNull();
    expect(badge!.label).toBe(label);
  });
});
