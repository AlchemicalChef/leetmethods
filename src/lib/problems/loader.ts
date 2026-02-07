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

// New problems
import orCommProblem from '@/content/problems/logic/or-commutative.json';
import existsWitnessProblem from '@/content/problems/logic/exists-witness.json';
import falseImpliesProblem from '@/content/problems/logic/false-implies-anything.json';
import plusAssocProblem from '@/content/problems/induction/plus-assoc.json';
import doublePlusProblem from '@/content/problems/induction/double-plus.json';
import listAppNilProblem from '@/content/problems/lists/list-app-nil.json';
import listMapIdProblem from '@/content/problems/lists/list-map-id.json';
import listFilterLengthProblem from '@/content/problems/lists/list-filter-length.json';
import subDiagProblem from '@/content/problems/arithmetic/sub-diag.json';
import mulCommProblem from '@/content/problems/arithmetic/mul-comm.json';
import evenOddDecProblem from '@/content/problems/arithmetic/even-odd-dec.json';
import treeLeafCountProblem from '@/content/problems/data-structures/tree-leaf-count.json';
import leAntisymProblem from '@/content/problems/relations/le-antisym.json';
import eqSymTransProblem from '@/content/problems/relations/eq-sym-trans.json';

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
  // New problems
  orCommProblem as Problem,
  existsWitnessProblem as Problem,
  falseImpliesProblem as Problem,
  plusAssocProblem as Problem,
  doublePlusProblem as Problem,
  listAppNilProblem as Problem,
  listMapIdProblem as Problem,
  listFilterLengthProblem as Problem,
  subDiagProblem as Problem,
  mulCommProblem as Problem,
  evenOddDecProblem as Problem,
  treeLeafCountProblem as Problem,
  leAntisymProblem as Problem,
  eqSymTransProblem as Problem,
];

export async function getAllProblems(): Promise<Problem[]> {
  return problems;
}

export function getAllProblemsSync(): Problem[] {
  return problems;
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

