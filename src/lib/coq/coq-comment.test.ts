import { describe, it, expect } from 'vitest';
import {
  stripCoqComments,
  isInsideCoqComment,
  skipCoqComment,
  splitHypNames,
} from './coq-comment';

describe('coq-comment', () => {
  describe('stripCoqComments', () => {
    it('returns unchanged code when no comments present', () => {
      const code = 'Theorem foo : forall x, x = x.';
      expect(stripCoqComments(code)).toBe(code);
    });

    it('removes a single comment', () => {
      const code = 'Theorem foo (* comment *) : Prop.';
      expect(stripCoqComments(code)).toBe('Theorem foo  : Prop.');
    });

    it('removes nested comments', () => {
      const code = 'A (* outer (* inner *) outer *) B';
      expect(stripCoqComments(code)).toBe('A  B');
    });

    it('preserves comments inside strings', () => {
      const code = 'Definition s := "text (* not a comment *) text".';
      expect(stripCoqComments(code)).toBe(code);
    });

    it('preserves strings with escaped quotes', () => {
      const code = 'Definition s := "a""b".';
      expect(stripCoqComments(code)).toBe(code);
    });

    it('removes multiple comments', () => {
      const code = 'A (* c1 *) B (* c2 *) C';
      expect(stripCoqComments(code)).toBe('A  B  C');
    });

    it('removes comment at start of code', () => {
      const code = '(* header *) Theorem foo.';
      expect(stripCoqComments(code)).toBe(' Theorem foo.');
    });

    it('removes comment at end of code', () => {
      const code = 'Theorem foo. (* footer *)';
      expect(stripCoqComments(code)).toBe('Theorem foo. ');
    });

    it('handles empty string', () => {
      expect(stripCoqComments('')).toBe('');
    });

    it('preserves code between two comments', () => {
      const code = '(* c1 *) middle (* c2 *)';
      expect(stripCoqComments(code)).toBe(' middle ');
    });

    it('does not treat opening delimiter inside string as comment start', () => {
      const code = 'Definition s := "(*". (* real comment *) X';
      expect(stripCoqComments(code)).toBe('Definition s := "(*".  X');
    });

    it('strips remainder when comment is unclosed', () => {
      const code = 'A (* unclosed comment';
      expect(stripCoqComments(code)).toBe('A ');
    });

    it('preserves closing delimiter inside string', () => {
      const code = 'Definition s := "*)". X';
      expect(stripCoqComments(code)).toBe(code);
    });

    it('handles escaped quotes at end of string before comment', () => {
      const code = '"a""" (* comment *)';
      expect(stripCoqComments(code)).toBe('"a""" ');
    });
  });

  describe('isInsideCoqComment', () => {
    it('returns false when position is outside any comment', () => {
      const text = 'Theorem foo.';
      expect(isInsideCoqComment(text, 5)).toBe(false);
    });

    it('returns true when position is inside a comment', () => {
      const text = 'A (* comment *) B';
      expect(isInsideCoqComment(text, 6)).toBe(true);
    });

    it('returns true when position is inside nested comment', () => {
      const text = 'A (* outer (* inner *) *) B';
      expect(isInsideCoqComment(text, 15)).toBe(true);
    });

    it('returns false when position is after closed comment', () => {
      const text = 'A (* comment *) B';
      expect(isInsideCoqComment(text, 16)).toBe(false);
    });

    it('returns false when position is inside string that looks like comment', () => {
      const text = 'Definition s := "(*".';
      expect(isInsideCoqComment(text, 18)).toBe(false);
    });

    it('returns false when pos is 0', () => {
      const text = '(* comment *)';
      expect(isInsideCoqComment(text, 0)).toBe(false);
    });

    it('handles pos beyond text length safely', () => {
      const text = 'A (* comment *) B';
      expect(isInsideCoqComment(text, 100)).toBe(false);
    });

    it('returns true when comment is unclosed at position', () => {
      const text = 'A (* unclosed';
      expect(isInsideCoqComment(text, 10)).toBe(true);
    });

    it('returns false at exact comment opening', () => {
      const text = 'A (* comment *) B';
      expect(isInsideCoqComment(text, 2)).toBe(false);
    });

    it('returns true right after comment opening', () => {
      const text = 'A (* comment *) B';
      expect(isInsideCoqComment(text, 4)).toBe(true);
    });
  });

  describe('skipCoqComment', () => {
    it('returns position after simple comment', () => {
      const code = 'A (* abc *) B';
      const result = skipCoqComment(code, 2);
      expect(result).toBe(11);
      expect(code[result]).toBe(' ');
    });

    it('returns position after nested comment', () => {
      const code = 'A (* (* inner *) outer *) B';
      const result = skipCoqComment(code, 2);
      expect(result).toBe(25);
      expect(code[result]).toBe(' ');
    });

    it('returns code length when comment is unclosed', () => {
      const code = 'A (* unclosed';
      const result = skipCoqComment(code, 2);
      expect(result).toBe(code.length);
    });

    it('handles comment at end of string', () => {
      const code = 'A (* comment *)';
      const result = skipCoqComment(code, 2);
      expect(result).toBe(15);
    });

    it('handles deeply nested comments (3 levels)', () => {
      const code = 'A (* l1 (* l2 (* l3 *) *) *) B';
      const result = skipCoqComment(code, 2);
      expect(result).toBe(28);
      expect(code[result]).toBe(' ');
    });

    it('handles empty comment', () => {
      const code = 'A (**) B';
      const result = skipCoqComment(code, 2);
      expect(result).toBe(6);
      expect(code[result]).toBe(' ');
    });
  });

  describe('splitHypNames', () => {
    it('returns single name', () => {
      expect(splitHypNames('H')).toEqual(['H']);
    });

    it('splits comma-separated names with spaces', () => {
      expect(splitHypNames('H1, H2, H3')).toEqual(['H1', 'H2', 'H3']);
    });

    it('returns empty array for empty string', () => {
      expect(splitHypNames('')).toEqual([]);
    });

    it('filters out empty entries from extra commas', () => {
      expect(splitHypNames('H1,,H2')).toEqual(['H1', 'H2']);
    });

    it('filters out whitespace-only entries', () => {
      expect(splitHypNames('H1,  ,H2')).toEqual(['H1', 'H2']);
    });

    it('trims whitespace from names', () => {
      expect(splitHypNames('  H1  ,  H2  ')).toEqual(['H1', 'H2']);
    });

    it('handles single comma', () => {
      expect(splitHypNames(',')).toEqual([]);
    });

    it('handles names without spaces after commas', () => {
      expect(splitHypNames('H1,H2,H3')).toEqual(['H1', 'H2', 'H3']);
    });
  });
});
