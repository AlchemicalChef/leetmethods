import type { VerificationResult, CoqGoal, CoqMessage } from './types';

// FIX #3: Don't use global flag to avoid regex state issues
// Instead, create fresh regex each time or use test without global flag
const FORBIDDEN_TACTICS_PATTERNS: Record<string, RegExp> = {
  admit: /\badmit\b/i,      // Removed 'g' flag
  Admitted: /\bAdmitted\b/, // Removed 'g' flag
  Abort: /\bAbort\b/,       // Removed 'g' flag
};

export function checkForbiddenTactics(
  code: string,
  forbiddenTactics: string[]
): { hasForbidden: boolean; found: string[] } {
  const found: string[] = [];

  for (const tactic of forbiddenTactics) {
    const pattern = FORBIDDEN_TACTICS_PATTERNS[tactic];
    if (pattern && pattern.test(code)) {
      found.push(tactic);
    }
  }

  return {
    hasForbidden: found.length > 0,
    found,
  };
}

export function isProofComplete(code: string): boolean {
  // Check if code ends with Qed. (allowing for whitespace/comments after)
  const qedPattern = /\bQed\s*\.\s*(?:$|\(\*[\s\S]*?\*\)\s*$)/m;
  return qedPattern.test(code);
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

export function parseGoalsFromHtml(html: string): CoqGoal[] {
  // jsCoq returns goals as HTML, parse them into structured data
  const goals: CoqGoal[] = [];

  // Match goal blocks - create fresh regex for each call
  const goalPattern = /<div class="goal[^"]*"[^>]*>([\s\S]*?)<\/div>/gi;
  let match;
  let id = 1;

  while ((match = goalPattern.exec(html)) !== null) {
    const goalHtml = match[1];

    // Extract hypotheses - create fresh regex for each goal
    const hypPattern = /<span class="hyp-name[^"]*">([^<]+)<\/span>[^<]*<span class="hyp-type[^"]*">([^<]+)<\/span>/gi;
    const hypotheses: { name: string; type: string }[] = [];
    let hypMatch;

    while ((hypMatch = hypPattern.exec(goalHtml)) !== null) {
      hypotheses.push({
        name: hypMatch[1].trim(),
        type: hypMatch[2].trim(),
      });
    }

    // Extract conclusion
    const conclusionPattern = /<span class="goal-conclusion[^"]*">([^<]+)<\/span>/i;
    const conclusionMatch = goalHtml.match(conclusionPattern);
    const conclusion = conclusionMatch ? conclusionMatch[1].trim() : '';

    goals.push({ id: id++, hypotheses, conclusion });
  }

  return goals;
}

export function parseGoalsFromText(text: string): CoqGoal[] {
  // Parse text-format goals (fallback)
  const goals: CoqGoal[] = [];
  const lines = text.split('\n');

  let currentGoal: CoqGoal | null = null;
  let inHypotheses = true;

  for (const line of lines) {
    const trimmed = line.trim();

    // Goal separator
    if (trimmed.match(/^=+$/)) {
      inHypotheses = false;
      continue;
    }

    // New goal indicator
    if (trimmed.match(/^\d+ (?:goal|subgoal)/i)) {
      continue;
    }

    if (inHypotheses && trimmed.includes(':')) {
      const [name, ...typeParts] = trimmed.split(':');
      if (currentGoal) {
        currentGoal.hypotheses.push({
          name: name.trim(),
          type: typeParts.join(':').trim(),
        });
      }
    } else if (!inHypotheses && trimmed) {
      if (!currentGoal) {
        currentGoal = {
          id: goals.length + 1,
          hypotheses: [],
          conclusion: trimmed,
        };
        goals.push(currentGoal);
      } else {
        currentGoal.conclusion += ' ' + trimmed;
      }
    }
  }

  return goals;
}
