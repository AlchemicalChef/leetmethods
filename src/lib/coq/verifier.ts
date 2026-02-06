import type { VerificationResult, CoqGoal, CoqMessage } from './types';

// Known forbidden tactic patterns with specific regex handling
const FORBIDDEN_TACTICS_PATTERNS: Record<string, RegExp> = {
  admit: /\badmit\b/,
  Admitted: /\bAdmitted\b/,
  Abort: /\bAbort\b/,
  Axiom: /\bAxiom\b/,
  Parameter: /\bParameter\b/,
  Conjecture: /\bConjecture\b/,
};

/** Strip Coq comments before checking for forbidden tactics */
function stripCoqComments(code: string): string {
  let result = '';
  let depth = 0;
  for (let i = 0; i < code.length; i++) {
    if (code[i] === '(' && code[i + 1] === '*') {
      depth++;
      i++;
    } else if (code[i] === '*' && code[i + 1] === ')' && depth > 0) {
      depth--;
      i++;
    } else if (depth === 0) {
      result += code[i];
    }
  }
  return result;
}

export function checkForbiddenTactics(
  code: string,
  forbiddenTactics: string[]
): { hasForbidden: boolean; found: string[] } {
  const found: string[] = [];
  const stripped = stripCoqComments(code);

  for (const tactic of forbiddenTactics) {
    // Use known pattern or dynamically create a word-boundary regex
    const pattern = FORBIDDEN_TACTICS_PATTERNS[tactic]
      ?? new RegExp(`\\b${tactic.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\b`);
    if (pattern.test(stripped)) {
      found.push(tactic);
    }
  }

  return {
    hasForbidden: found.length > 0,
    found,
  };
}

export function isProofComplete(code: string): boolean {
  // Strip comments first to avoid matching Qed/Defined inside comments
  const stripped = stripCoqComments(code);
  const terminatorPattern = /\b(?:Qed|Defined)\s*\.\s*$/m;
  return terminatorPattern.test(stripped.trim());
}

export function createVerificationResult(
  goals: CoqGoal[],
  messages: CoqMessage[],
  errors: string[],
  code: string,
  forbiddenTactics: string[]
): VerificationResult {
  const { hasForbidden, found } = checkForbiddenTactics(code, forbiddenTactics);
  const isComplete = goals.length === 0 && errors.length === 0 && isProofComplete(code);

  return {
    success: isComplete && !hasForbidden,
    goals,
    errors,
    messages,
    hasForbiddenTactics: hasForbidden,
    forbiddenTacticsFound: found,
    isComplete: isComplete && !hasForbidden,
  };
}

