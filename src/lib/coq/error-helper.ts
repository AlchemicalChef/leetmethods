interface ErrorPattern {
  pattern: RegExp;
  friendly: (match: RegExpMatchArray) => string;
}

const errorPatterns: ErrorPattern[] = [
  {
    pattern: /Unable to unify "(.+)" with "(.+)"/,
    friendly: (m) => `Type mismatch: expected "${m[2]}" but got "${m[1]}". Check that your expression has the right type.`,
  },
  {
    pattern: /No more subgoals/,
    friendly: () => `The proof is already complete! Remove extra tactics after Qed.`,
  },
  {
    pattern: /Not a proposition or a type/,
    friendly: () => `This expression isn't a proposition. Make sure you're proving a logical statement.`,
  },
  {
    pattern: /The variable (.+) was not found/,
    friendly: (m) => `Unknown variable "${m[1]}". Did you forget to introduce it with "intros"?`,
  },
  {
    pattern: /Unable to find an instance/,
    friendly: () => `Coq can't automatically find a matching value. Try providing it explicitly.`,
  },
  {
    pattern: /The term "(.+)" has type "(.+)" while it is expected to have type "(.+)"/,
    friendly: (m) => `Wrong type: "${m[1]}" is a "${m[2]}" but needs to be a "${m[3]}".`,
  },
  {
    pattern: /In environment[\s\S]*?The term/,
    friendly: () => `Type error in the current proof context. Check that your tactic arguments match the goal.`,
  },
  {
    pattern: /No such goal/,
    friendly: () => `There's no goal to prove. You may have already completed this part.`,
  },
  {
    pattern: /Syntax error/,
    friendly: () => `Syntax error in your Coq code. Check for missing periods, parentheses, or typos.`,
  },
  {
    pattern: /The reference (.+) was not found/,
    friendly: (m) => `"${m[1]}" is not defined. Check the spelling or make sure the required library is imported.`,
  },
  {
    pattern: /No matching clauses for match/,
    friendly: () => `Pattern match is incomplete. Make sure you handle all cases.`,
  },
  {
    pattern: /Cannot find a physical path/,
    friendly: () => `A required library could not be found. This may be a configuration issue.`,
  },
  {
    pattern: /Tactic failure/,
    friendly: () => `The tactic failed. The current goal may not match what the tactic expects.`,
  },
];

export interface FormattedError {
  raw: string;
  friendly: string | null;
}

export function formatCoqError(rawError: string): FormattedError {
  for (const { pattern, friendly } of errorPatterns) {
    const match = rawError.match(pattern);
    if (match) {
      return { raw: rawError, friendly: friendly(match) };
    }
  }
  return { raw: rawError, friendly: null };
}
