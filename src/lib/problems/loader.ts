/**
 * Problem loader and registry for LeetMethods.
 *
 * This module is the single source of truth for all built-in Coq problems.
 * It statically imports every problem JSON file and provides synchronous
 * accessor functions to retrieve them.
 *
 * Key design decisions:
 * - **Static imports**: Problems are imported at build time, not loaded from
 *   the filesystem at runtime. This is necessary because the app is client-side
 *   only (no Node.js filesystem access). New problems must be manually added
 *   to both the import list and the `problems` array below.
 * - **Synchronous API**: `getAllProblems()` and `getProblemSummaries()` are
 *   synchronous functions (not async). This simplifies usage in React components
 *   and avoids unnecessary loading states.
 * - **Type assertion**: JSON imports are cast `as Problem` because TypeScript
 *   cannot verify JSON structure against the interface at compile time. The
 *   problem JSON schema is validated by convention and test coverage.
 *
 * Problem JSON files live in `src/content/problems/{category}/` and follow
 * the `Problem` interface defined in `./types.ts`.
 *
 * @module problems/loader
 */

import type { Problem, ProblemSummary } from './types';

/* ============================================================================
 * Static Problem Imports
 *
 * Each problem JSON file is imported individually. This is verbose but necessary
 * for the client-side-only architecture. Webpack/Next.js can tree-shake and
 * bundle these efficiently since they are static imports.
 * ========================================================================= */

/* -- Logic category -- */
import modusPonensProblem from '@/content/problems/logic/modus-ponens.json';
import doubleNegationProblem from '@/content/problems/logic/double-negation.json';
import andCommProblem from '@/content/problems/logic/and-commutative.json';
import orCommProblem from '@/content/problems/logic/or-commutative.json';
import existsWitnessProblem from '@/content/problems/logic/exists-witness.json';
import falseImpliesProblem from '@/content/problems/logic/false-implies-anything.json';
import contrapositiveProblem from '@/content/problems/logic/contrapositive.json';
import iffSymmetricProblem from '@/content/problems/logic/iff-symmetric.json';

/* -- Induction category -- */
import plusNZeroProblem from '@/content/problems/induction/plus-n-zero.json';
import plusCommProblem from '@/content/problems/induction/plus-comm.json';
import multNZeroProblem from '@/content/problems/induction/mult-n-zero.json';
import plusAssocProblem from '@/content/problems/induction/plus-assoc.json';
import doublePlusProblem from '@/content/problems/induction/double-plus.json';
import plusNSmProblem from '@/content/problems/induction/plus-n-sm.json';
import mul1RProblem from '@/content/problems/induction/mul-1-r.json';

/* -- Lists category -- */
import listLengthAppProblem from '@/content/problems/lists/list-length-app.json';
import listRevRevProblem from '@/content/problems/lists/list-rev-rev.json';
import listAppNilProblem from '@/content/problems/lists/list-app-nil.json';
import listMapIdProblem from '@/content/problems/lists/list-map-id.json';
import listFilterLengthProblem from '@/content/problems/lists/list-filter-length.json';
import listAppAssocProblem from '@/content/problems/lists/list-app-assoc.json';
import listRevLengthProblem from '@/content/problems/lists/list-rev-length.json';

/* -- Arithmetic category -- */
import evenDoubleProblem from '@/content/problems/arithmetic/even-double.json';
import subDiagProblem from '@/content/problems/arithmetic/sub-diag.json';
import mulCommProblem from '@/content/problems/arithmetic/mul-comm.json';
import evenOddDecProblem from '@/content/problems/arithmetic/even-odd-dec.json';
import add1RProblem from '@/content/problems/arithmetic/add-1-r.json';

/* -- Data Structures category -- */
import treeMirrorProblem from '@/content/problems/data-structures/tree-mirror.json';
import treeSizeNodeProblem from '@/content/problems/data-structures/tree-size-node.json';
import bstInsertMemberProblem from '@/content/problems/data-structures/bst-insert-member.json';
import treeLeafCountProblem from '@/content/problems/data-structures/tree-leaf-count.json';
import swapInvolutiveProblem from '@/content/problems/data-structures/swap-involutive.json';

/* -- Relations category -- */
import leReflProblem from '@/content/problems/relations/le-refl.json';
import leTransProblem from '@/content/problems/relations/le-trans.json';
import eqPairProblem from '@/content/problems/relations/eq-pair.json';
import leAntisymProblem from '@/content/problems/relations/le-antisym.json';
import eqSymTransProblem from '@/content/problems/relations/eq-sym-trans.json';
import eqSymmetryProblem from '@/content/problems/relations/eq-symmetry.json';

/* -- Booleans category -- */
import negbInvolutiveProblem from '@/content/problems/booleans/negb-involutive.json';
import andbCommProblem from '@/content/problems/booleans/andb-comm.json';
import andbTrueIffProblem from '@/content/problems/booleans/andb-true-iff.json';
import orbTrueIffProblem from '@/content/problems/booleans/orb-true-iff.json';

/* ============================================================================
 * Problem Registry
 *
 * The master array of all problems in the application. The order here
 * determines the default display order when no sorting is applied.
 * New problems must be added to this array to be visible in the app.
 * ========================================================================= */

/**
 * The complete, ordered list of all built-in problems.
 *
 * Each JSON import is cast to `Problem` since TypeScript cannot statically
 * verify the structure of JSON imports against the interface.
 */
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
  treeMirrorProblem as Problem,
  treeSizeNodeProblem as Problem,
  bstInsertMemberProblem as Problem,
  leReflProblem as Problem,
  leTransProblem as Problem,
  eqPairProblem as Problem,
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
  negbInvolutiveProblem as Problem,
  andbCommProblem as Problem,
  andbTrueIffProblem as Problem,
  orbTrueIffProblem as Problem,
  contrapositiveProblem as Problem,
  iffSymmetricProblem as Problem,
  plusNSmProblem as Problem,
  mul1RProblem as Problem,
  listAppAssocProblem as Problem,
  listRevLengthProblem as Problem,
  swapInvolutiveProblem as Problem,
  eqSymmetryProblem as Problem,
  add1RProblem as Problem,
];

/* ============================================================================
 * Public API
 * ========================================================================= */

/**
 * Returns the full list of all built-in problems with complete data.
 *
 * This includes all fields (description, hints, prelude, template, solution,
 * forbiddenTactics, prerequisites) needed for the problem solver page.
 *
 * The returned array is the same reference as the internal `problems` array,
 * so callers should treat it as read-only.
 *
 * @returns All registered problems with full detail.
 */
export function getAllProblems(): Problem[] {
  return problems;
}

/**
 * Returns lightweight summaries of all built-in problems.
 *
 * Strips out the heavy fields (description, hints, template, solution, prelude,
 * forbiddenTactics) to provide only the metadata needed for listing pages
 * (the problems index page, recommendation engine, statistics computation).
 *
 * Unlike `getAllProblems()`, this creates new objects on each call, so it is
 * slightly less efficient but safe to mutate.
 *
 * @returns An array of `ProblemSummary` objects with ID, slug, title,
 *          difficulty, category, and tags.
 */
export function getProblemSummaries(): ProblemSummary[] {
  return problems.map(({ id, slug, title, difficulty, category, tags }) => ({
    id,
    slug,
    title,
    difficulty,
    category,
    tags,
  }));
}
