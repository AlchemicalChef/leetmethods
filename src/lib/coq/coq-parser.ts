import type { CoqGoal } from './types';

/** Recursively convert a Pp AST (nested arrays) to plain text */
export function ppToString(pp: unknown): string {
  if (typeof pp === 'string') return pp;
  if (!Array.isArray(pp)) return String(pp);
  const tag = pp[0];
  if (tag === 'Pp_string') return (pp[1] as string) || '';
  if (tag === 'Pp_glue' || tag === 'Pp_box') return ((pp[1] as unknown[]) || []).map(c => ppToString(c)).join('');
  if (tag === 'Pp_tag') return ppToString(pp[2]);
  if (tag === 'Pp_force_newline' || tag === 'Pp_print_break') return ' ';
  return pp.slice(1).map((c: unknown) => ppToString(c)).join('');
}

/** Convert Pp AST or tagged string to plain text */
export function stripPpTags(s: unknown): string {
  if (Array.isArray(s)) return ppToString(s);
  if (typeof s !== 'string') return String(s);
  return s.replace(/<\/?Pp_[^>]*>/g, '').replace(/<\/?[a-z_]+>/gi, '').trim();
}

/**
 * Parse raw jsCoq goal data into typed CoqGoal array.
 * jsCoq hypotheses are 3-element tuples: [names, definition, type]
 * where definition is null/undefined for regular (non-let) hypotheses.
 */
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export function parseGoalData(goalData: any): CoqGoal[] {
  if (!goalData?.goals) return [];

  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  return goalData.goals.map((g: any, index: number) => ({
    id: index + 1,
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    hypotheses: (g.hyp || []).map((h: any) => ({
      name: (Array.isArray(h[0]) ? h[0] : [h[0]]).join(', '),
      type: stripPpTags(h[2] ?? h[1]),
    })),
    conclusion: stripPpTags(g.ccl),
  }));
}

/** Check if a statement is a Proof command (not inside comments/strings) */
export function isProofStart(statement: string): boolean {
  // Strip comments
  const noComments = statement.replace(/\(\*[\s\S]*?\*\)/g, '');
  // Strip strings
  const noStrings = noComments.replace(/"[^"]*"/g, '');
  return /^\s*Proof\b/i.test(noStrings);
}

export function parseStatements(code: string): string[] {
  const statements: string[] = [];
  let current = '';
  let commentDepth = 0;
  let inString = false;

  for (let i = 0; i < code.length; i++) {
    const char = code[i];
    const next = code[i + 1];

    if (char === '(' && next === '*' && !inString) {
      commentDepth++;
      current += '(*';
      i++;
      continue;
    }

    if (char === '*' && next === ')' && commentDepth > 0 && !inString) {
      commentDepth--;
      current += '*)';
      i++;
      continue;
    }

    // Coq uses "" for escaped quotes inside strings (not backslash)
    if (char === '"' && commentDepth === 0) {
      if (inString && next === '"') {
        // Escaped quote inside string: ""
        current += '""';
        i++;
        continue;
      }
      inString = !inString;
    }

    current += char;

    // Coq sentence terminator: . followed by whitespace or EOF
    // This avoids splitting on . in qualified names like Nat.compare
    if (char === '.' && commentDepth === 0 && !inString) {
      const nextChar = code[i + 1];
      if (nextChar === undefined || /\s/.test(nextChar)) {
        const trimmed = current.trim();
        if (trimmed) {
          statements.push(trimmed);
        }
        current = '';
      }
    }
  }

  return statements;
}
