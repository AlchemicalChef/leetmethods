/**
 * @module coq-syntax
 *
 * Coq syntax highlighting definition for CodeMirror 6.
 *
 * Provides a `StreamLanguage`-based tokenizer that highlights Coq source code
 * in the editor. CodeMirror 6's `StreamLanguage` adapter allows using a simple
 * character-by-character tokenizer (similar to CodeMirror 5's mode API) rather
 * than requiring a full Lezer grammar.
 *
 * ## Token Categories
 *
 * The tokenizer classifies Coq tokens into these CodeMirror highlight categories:
 * - **keyword**: Vernacular commands (Theorem, Lemma, Proof, Qed, etc.) and bullet points
 * - **function**: Tactic names (intros, apply, rewrite, etc.)
 * - **type**: Built-in types (nat, bool, Prop, etc.)
 * - **builtin**: Language built-ins (forall, exists, fun, match, etc.)
 * - **className**: Uppercase identifiers (likely constructors like S, O, cons, etc.)
 * - **variableName**: Lowercase identifiers (variables, function names)
 * - **comment**: Everything inside `(* ... *)` (supports nesting)
 * - **string**: Everything inside `"..."` (supports `""` escaped quotes)
 * - **number**: Decimal and hexadecimal integer literals
 * - **operator**: Operator characters (=, +, -, *, ->, etc.)
 * - **punctuation**: Period (sentence terminator)
 * - **bracket**: Parentheses, braces, square brackets
 *
 * ## Design Decisions
 *
 * - Uses `StreamLanguage` rather than a Lezer grammar because Coq's syntax is
 *   complex (dependent types, tactic languages, etc.) and a full parser would be
 *   overkill for highlighting. Stream-based tokenization is sufficient and much
 *   simpler to maintain.
 * - Keywords, tactics, and types are stored in flat arrays and checked via
 *   `includes()`. This is fast enough for the small vocabulary sizes involved
 *   (~60 keywords, ~50 tactics, ~15 types).
 * - Bullet points (`-`, `+`, `*`) at the start of a line are highlighted as
 *   keywords because they serve as Coq proof structuring commands.
 * - Constructors (uppercase identifiers) get `className` highlighting to
 *   visually distinguish them from variables in pattern matches and definitions.
 *
 * @see CoqEditor component - The CodeMirror editor that consumes this language definition
 * @see coq-autocomplete.ts - Autocomplete integration for the same editor
 * @see coq-hover.ts - Hover tooltip integration for the same editor
 */
import { StreamLanguage } from '@codemirror/language';

/* ==============================================================================
 * Token Vocabularies
 * ==============================================================================
 * These arrays define the known Coq identifiers for each syntactic category.
 * They are used during tokenization to classify identifier tokens.
 * =========================================================================== */

/**
 * Coq vernacular commands (top-level keywords).
 * These are the commands that structure Coq files: defining theorems, modules,
 * notations, and controlling the proof environment.
 */
const coqKeywords = [
  'Theorem', 'Lemma', 'Proof', 'Qed', 'Defined', 'Admitted', 'Abort',
  'Definition', 'Fixpoint', 'CoFixpoint', 'Inductive', 'CoInductive',
  'Record', 'Structure', 'Class', 'Instance',
  'Section', 'Module', 'End', 'Import', 'Export', 'Require', 'Open', 'Scope',
  'Notation', 'Infix', 'Arguments',
  'Variable', 'Variables', 'Hypothesis', 'Hypotheses', 'Parameter', 'Parameters',
  'Axiom', 'Axioms', 'Conjecture',
  'Let', 'Context', 'Existing',
  'Check', 'Print', 'Compute', 'Eval', 'Search', 'SearchAbout', 'SearchPattern',
  'Goal', 'Example', 'Fact', 'Remark', 'Corollary', 'Proposition',
  'Set', 'Unset', 'Ltac', 'Tactic',
];

/**
 * Coq proof tactics. These are the commands used inside proof mode to
 * manipulate goals and hypotheses. Highlighted as "function" since they
 * behave like function calls within the proof.
 */
const coqTactics = [
  'intros', 'intro', 'apply', 'exact', 'assumption', 'trivial', 'auto', 'eauto',
  'reflexivity', 'symmetry', 'transitivity',
  'rewrite', 'replace', 'subst', 'unfold', 'fold', 'simpl', 'cbv', 'lazy',
  'destruct', 'induction', 'case', 'case_eq', 'elim', 'inversion', 'injection',
  'split', 'left', 'right', 'exists', 'constructor', 'econstructor',
  'assert', 'pose', 'set', 'remember', 'cut', 'enough', 'specialize',
  'generalize', 'dependent', 'clear', 'clearbody', 'rename', 'move', 'revert',
  'exfalso', 'contradiction', 'discriminate', 'congruence', 'omega', 'lia', 'ring',
  'field', 'fourier', 'nia', 'psatz',
  'repeat', 'try', 'do', 'progress', 'solve', 'now', 'first', 'fail', 'idtac',
  'f_equal', 'change', 'pattern', 'vm_compute', 'native_compute',
  'admit', 'give_up',
];

/**
 * Built-in Coq types and type-level constants. These are the foundational
 * types in the Calculus of Inductive Constructions and commonly used
 * standard library types.
 */
const coqTypes = [
  'Type', 'Prop', 'Set', 'SProp',
  'nat', 'bool', 'list', 'option', 'unit', 'Empty_set',
  'True', 'False', 'eq', 'and', 'or', 'not', 'iff', 'ex', 'sig',
];

/**
 * Coq language built-ins that are part of the term language (not vernacular
 * commands or tactics). These include quantifiers, match expressions,
 * let-bindings, and fixpoint constructs.
 */
const coqBuiltins = [
  'forall', 'exists', 'fun', 'match', 'with', 'end', 'as', 'in', 'return', 'if', 'then', 'else',
  'let', 'fix', 'cofix', 'struct', 'where', 'for',
];

/**
 * Regex for matching Coq operator characters. Coq allows a wide range of
 * operator symbols, including mathematical notation characters.
 */
const coqOperators = /^[=<>+\-*/\\|&!@#$%^~?:]+/;

/* ==============================================================================
 * Stream Language Definition
 * ==============================================================================
 * The tokenizer is defined using CodeMirror 6's StreamLanguage API, which
 * processes one token at a time. State is carried between tokens to track
 * multi-token constructs (nested comments and multi-line strings).
 * =========================================================================== */

/**
 * CodeMirror 6 language definition for Coq.
 *
 * Uses the StreamLanguage adapter which provides a simpler tokenization API
 * than a full Lezer grammar. The tokenizer maintains two pieces of state:
 * - `inComment`: Nesting depth of `(* ... *)` comments (0 = not in comment)
 * - `inString`: Whether we're inside a `"..."` string literal
 *
 * These state values persist across lines, enabling correct highlighting of
 * multi-line comments and strings.
 */
const coqLanguage = StreamLanguage.define({
  name: 'coq',

  /**
   * Initial parser state. Both comment depth and string flag start at their
   * "not inside" values.
   */
  startState() {
    return {
      inComment: 0,
      inString: false,
    };
  },

  /**
   * Tokenizes one token from the stream.
   *
   * The token function is called repeatedly by CodeMirror to classify each
   * piece of the source code. It reads characters from `stream` and returns
   * the token type string (or null for unhighlighted text).
   *
   * @param stream - The character stream to read from
   * @param state - Mutable state carried between tokens (comment depth, string flag)
   * @returns Token type string for highlighting, or null for default styling
   */
  token(stream, state) {
    // --- Multi-line nested comments ---
    // If we're inside a comment, keep consuming until we find the matching `*)`
    // while tracking nested `(*` to handle Coq's nested comment syntax
    if (state.inComment > 0) {
      if (stream.match('*)')) {
        state.inComment--;
        return 'comment';
      }
      if (stream.match('(*')) {
        state.inComment++;
        return 'comment';
      }
      stream.next();
      return 'comment';
    }

    // --- Start of a new comment ---
    if (stream.match('(*')) {
      state.inComment = 1;
      return 'comment';
    }

    // --- String literals ---
    // Handles Coq's `""` escape convention for embedded quote characters.
    // When we encounter a `"` that is followed by another `"`, it's an escaped
    // quote inside the string, not the end of the string.
    if (state.inString || stream.peek() === '"') {
      if (!state.inString) {
        stream.next();
        state.inString = true;
      }
      while (!stream.eol()) {
        if (stream.next() === '"') {
          if (stream.peek() === '"') {
            stream.next(); // Consume the second quote; remain in string state
          } else {
            state.inString = false;
            break;
          }
        }
      }
      return 'string';
    }

    // --- Whitespace ---
    if (stream.eatSpace()) {
      return null;
    }

    // --- Proof bullet points ---
    // In Coq, `-`, `+`, and `*` at the start of a line (after optional whitespace)
    // are proof structuring bullets. They help organize proofs with multiple subgoals.
    if (stream.string.slice(0, stream.pos).match(/^\s*$/)) {
      if (stream.match(/^[-+*]+(?=\s|$)/)) {
        return 'keyword';
      }
    }

    // --- Numeric literals ---
    // Supports both hexadecimal (0xFF) and decimal (42) integer literals
    if (stream.match(/^0[xX][0-9a-fA-F]+/) || stream.match(/^\d+/)) {
      return 'number';
    }

    // --- Identifiers and keywords ---
    // Coq identifiers can contain letters, digits, underscores, and primes (')
    if (stream.match(/^[a-zA-Z_][a-zA-Z0-9_']*/)) {
      const word = stream.current();
      if (coqKeywords.includes(word)) {
        return 'keyword';
      }
      if (coqTactics.includes(word)) {
        return 'function';
      }
      if (coqTypes.includes(word)) {
        return 'type';
      }
      if (coqBuiltins.includes(word)) {
        return 'builtin';
      }
      // Uppercase identifiers are likely constructors (S, O, cons, Some, None, etc.)
      if (/^[A-Z]/.test(word)) {
        return 'className';
      }
      return 'variableName';
    }

    // --- Period (sentence terminator) ---
    if (stream.match('.')) {
      return 'punctuation';
    }

    // --- Operators ---
    if (stream.match(coqOperators)) {
      return 'operator';
    }

    // --- Brackets ---
    if (stream.match(/^[(){}[\]]/)) {
      return 'bracket';
    }

    // --- Fallback: consume one character ---
    // Any unrecognized character is consumed without highlighting
    stream.next();
    return null;
  },
});

export { coqLanguage };
