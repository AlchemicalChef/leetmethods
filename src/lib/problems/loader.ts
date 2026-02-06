import type { Problem, ProblemSummary } from './types';

// Import all problem JSON files
// In a real app, this would read from the filesystem or database
import modusPonensProblem from '@/content/problems/logic/modus-ponens.json';
import doubleNegationProblem from '@/content/problems/logic/double-negation.json';
import andCommProblem from '@/content/problems/logic/and-commutative.json';
import plusNZeroProblem from '@/content/problems/induction/plus-n-zero.json';
import plusCommProblem from '@/content/problems/induction/plus-comm.json';
import multNZeroProblem from '@/content/problems/induction/mult-n-zero.json';
import listLengthAppProblem from '@/content/problems/lists/list-length-app.json';
import listRevRevProblem from '@/content/problems/lists/list-rev-rev.json';
import evenDoubleProblem from '@/content/problems/arithmetic/even-double.json';
import addAssocProblem from '@/content/problems/arithmetic/add-assoc.json';
import treeMirrorProblem from '@/content/problems/data-structures/tree-mirror.json';
import treeSizeNodeProblem from '@/content/problems/data-structures/tree-size-node.json';
import bstInsertMemberProblem from '@/content/problems/data-structures/bst-insert-member.json';
import leReflProblem from '@/content/problems/relations/le-refl.json';
import leTransProblem from '@/content/problems/relations/le-trans.json';
import eqPairProblem from '@/content/problems/relations/eq-pair.json';

const problems: Problem[] = [
  modusPonensProblem as Problem,
  doubleNegationProblem as Problem,
  andCommProblem as Problem,
  plusNZeroProblem as Problem,
  plusCommProblem as Problem,
  multNZeroProblem as Problem,
  listLengthAppProblem as Problem,
  listRevRevProblem as Problem,
  evenDoubleProblem as Problem,
  addAssocProblem as Problem,
  treeMirrorProblem as Problem,
  treeSizeNodeProblem as Problem,
  bstInsertMemberProblem as Problem,
  leReflProblem as Problem,
  leTransProblem as Problem,
  eqPairProblem as Problem,
];

export async function getAllProblems(): Promise<Problem[]> {
  return problems;
}

export async function getProblemBySlug(slug: string): Promise<Problem | null> {
  return problems.find((p) => p.slug === slug) || null;
}

export async function getProblemSummaries(): Promise<ProblemSummary[]> {
  return problems.map(({ id, slug, title, difficulty, category, tags }) => ({
    id,
    slug,
    title,
    difficulty,
    category,
    tags,
  }));
}

export function getProblemsByCategory(category: string): Problem[] {
  return problems.filter((p) => p.category === category);
}

export function getProblemsByDifficulty(difficulty: string): Problem[] {
  return problems.filter((p) => p.difficulty === difficulty);
}
