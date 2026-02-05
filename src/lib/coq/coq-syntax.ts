import { StreamLanguage } from '@codemirror/language';

// Coq syntax highlighting for CodeMirror 6
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

const coqTypes = [
  'Type', 'Prop', 'Set', 'SProp',
  'nat', 'bool', 'list', 'option', 'unit', 'Empty_set',
  'True', 'False', 'eq', 'and', 'or', 'not', 'iff', 'ex', 'sig',
];

const coqBuiltins = [
  'forall', 'exists', 'fun', 'match', 'with', 'end', 'as', 'in', 'return', 'if', 'then', 'else',
  'let', 'fix', 'cofix', 'struct', 'where', 'for',
];

const coqOperators = /^[=<>+\-*/\\|&!@#$%^~?:]+/;

const coqLanguage = StreamLanguage.define({
  name: 'coq',
  startState() {
    return {
      inComment: 0,
      inString: false,
    };
  },
  token(stream, state) {
    // Handle multi-line comments (with nesting support)
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

    // Start of comment
    if (stream.match('(*')) {
      state.inComment = 1;
      return 'comment';
    }

    // Strings
    if (state.inString || stream.peek() === '"') {
      if (!state.inString) {
        stream.next();
        state.inString = true;
      }
      while (!stream.eol()) {
        if (stream.next() === '"') {
          state.inString = false;
          break;
        }
      }
      return 'string';
    }

    // Skip whitespace
    if (stream.eatSpace()) {
      return null;
    }

    // FIX #14: Bullet points at start of line (or after whitespace)
    // Match -, +, * followed by space or end of line (common pattern: "- reflexivity.")
    if (stream.sol() || stream.string.slice(0, stream.pos).match(/^\s*$/)) {
      if (stream.match(/^[-+*]+(?=\s|$)/)) {
        return 'keyword';
      }
    }
    // Also match standalone bullets (just the character)
    if (stream.match(/^[-+*](?=\s)/)) {
      return 'keyword';
    }

    // Numbers
    if (stream.match(/^0[xX][0-9a-fA-F]+/) || stream.match(/^\d+/)) {
      return 'number';
    }

    // Identifiers and keywords
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
      // Check if it's a constructor (starts with uppercase)
      if (/^[A-Z]/.test(word)) {
        return 'className';
      }
      return 'variableName';
    }

    // Dot (statement terminator)
    if (stream.match('.')) {
      return 'punctuation';
    }

    // Operators
    if (stream.match(coqOperators)) {
      return 'operator';
    }

    // Brackets
    if (stream.match(/^[(){}[\]]/)) {
      return 'bracket';
    }

    // Eat any other character
    stream.next();
    return null;
  },
});

export { coqLanguage };
