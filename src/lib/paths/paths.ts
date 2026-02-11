/**
 * Learning path definitions for LeetMethods.
 *
 * Each learning path is a curated, ordered sequence of problems that guides
 * the user through a specific topic area in Coq. Paths serve two purposes:
 *
 * 1. **Guided progression**: Users who are unsure what to do next can follow
 *    a path that introduces concepts in a pedagogically sound order.
 * 2. **Skill tracking**: The path progress system (`./progress.ts`) tracks
 *    which steps a user has completed, providing a sense of accomplishment.
 *
 * Paths are organized by difficulty:
 * - **beginner**: Foundational concepts (boolean case analysis, basic logic, first induction proofs).
 * - **intermediate**: More challenging proofs (advanced induction, list operations, arithmetic identities).
 * - **advanced**: Complex proofs requiring multiple techniques (data structures, relational reasoning).
 *
 * Each step's `problemSlug` must correspond to a problem registered in the
 * problem loader (`src/lib/problems/loader.ts`). The step's `title` and
 * `description` are displayed in the path UI and may differ from the problem's
 * own title to provide path-specific context.
 *
 * To add a new path: append a new `LearningPath` object to this array.
 * The path will automatically appear on the `/learn` page.
 *
 * @module paths/paths
 */

import type { LearningPath } from './types';

/**
 * The complete, ordered list of all learning paths available in the application.
 *
 * Paths are listed in display order (beginner first, advanced last).
 * Each path contains an ordered list of steps that reference problems by slug.
 */
export const learningPaths: LearningPath[] = [
  /* ========================================================================
   * Beginner Paths
   * ===================================================================== */

  {
    slug: 'boolean-basics',
    title: 'Boolean Basics',
    description: 'Get comfortable with case analysis on booleans. Learn to prove properties about negation, conjunction, and disjunction of boolean values.',
    difficulty: 'beginner',
    icon: '🔘',
    steps: [
      {
        problemSlug: 'negb-involutive',
        title: 'Negation is Involutive',
        description: 'Prove negb (negb b) = b by case analysis on booleans.',
      },
      {
        problemSlug: 'andb-comm',
        title: 'Boolean And is Commutative',
        description: 'Prove andb is commutative using case analysis.',
      },
      {
        problemSlug: 'andb-true-iff',
        title: 'And-True Equivalence',
        description: 'Prove the iff between andb and propositional conjunction.',
      },
      {
        problemSlug: 'orb-true-iff',
        title: 'Or-True Equivalence',
        description: 'Prove the iff between orb and propositional disjunction.',
      },
    ],
  },
  {
    slug: 'foundations-of-logic',
    title: 'Foundations of Logic',
    description: 'Master the basics of propositional logic in Coq. Learn intros, apply, exact, and how to work with implications, conjunctions, disjunctions, and equivalences.',
    difficulty: 'beginner',
    icon: '🧠',
    steps: [
      {
        problemSlug: 'modus-ponens',
        title: 'Modus Ponens',
        description: 'Learn intros and apply by proving the most basic logic rule.',
      },
      {
        problemSlug: 'double-negation',
        title: 'Double Negation Introduction',
        description: 'Work with negation — prove P implies ~~P.',
      },
      {
        problemSlug: 'and-commutative',
        title: 'And is Commutative',
        description: 'Use split, destruct, and left/right to work with conjunctions.',
      },
      {
        problemSlug: 'or-commutative',
        title: 'Or is Commutative',
        description: 'Use destruct on disjunctions and left/right to rebuild them.',
      },
      {
        problemSlug: 'contrapositive',
        title: 'Contrapositive',
        description: 'Chain implications to prove the contrapositive law.',
      },
      {
        problemSlug: 'iff-symmetric',
        title: 'Iff is Symmetric',
        description: 'Decompose and reconstruct logical equivalences.',
      },
    ],
  },
  {
    slug: 'introduction-to-induction',
    title: 'Introduction to Induction',
    description: 'Your first steps with proof by induction on natural numbers. Learn the base case + inductive step pattern.',
    difficulty: 'beginner',
    icon: '🔢',
    steps: [
      {
        problemSlug: 'plus-n-sm',
        title: 'n + S m = S (n + m)',
        description: 'A fundamental property of addition — your first induction proof.',
      },
      {
        problemSlug: 'add-1-r',
        title: 'n + 1 = S n',
        description: 'Prove a simple successor identity by induction.',
      },
      {
        problemSlug: 'mul-1-r',
        title: 'n * 1 = n',
        description: 'Practice induction with multiplication.',
      },
      {
        problemSlug: 'plus-n-zero',
        title: 'n + 0 = n',
        description: 'The classic right-identity of addition.',
      },
    ],
  },

  /* ========================================================================
   * Intermediate Paths
   * ===================================================================== */

  {
    slug: 'mastering-induction',
    title: 'Mastering Induction',
    description: 'Tackle harder induction proofs on natural numbers. Progress from simple base-step proofs to multi-variable induction.',
    difficulty: 'intermediate',
    icon: '🔄',
    steps: [
      {
        problemSlug: 'mult-n-zero',
        title: 'n * 0 = 0',
        description: 'Practice induction with multiplication properties.',
      },
      {
        problemSlug: 'even-double',
        title: 'Even Double',
        description: 'Combine induction with even/odd number properties.',
      },
      {
        problemSlug: 'plus-comm',
        title: 'Addition is Commutative',
        description: 'A more challenging induction that requires auxiliary lemmas.',
      },
      {
        problemSlug: 'double-plus',
        title: 'Double Equals Plus Self',
        description: 'Prove double n = n + n using induction and rewrite lemmas.',
      },
    ],
  },
  {
    slug: 'lists-and-append',
    title: 'Lists & Append',
    description: 'Prove properties about list operations. Learn structural induction on lists and how append interacts with other functions.',
    difficulty: 'intermediate',
    icon: '📋',
    steps: [
      {
        problemSlug: 'list-app-nil',
        title: 'Append Nil',
        description: 'Prove that appending nil is the identity — l ++ [] = l.',
      },
      {
        problemSlug: 'list-app-assoc',
        title: 'Append is Associative',
        description: 'Prove associativity of list append by induction.',
      },
      {
        problemSlug: 'list-map-id',
        title: 'Map Identity',
        description: 'Prove that mapping the identity function returns the same list.',
      },
      {
        problemSlug: 'list-filter-length',
        title: 'Filter Length',
        description: 'Prove that filtering never increases list length.',
      },
    ],
  },
  {
    slug: 'arithmetic-proofs',
    title: 'Arithmetic Proofs',
    description: 'Prove fundamental arithmetic properties. Combine induction with rewriting to establish key identities.',
    difficulty: 'intermediate',
    icon: '🔣',
    steps: [
      {
        problemSlug: 'sub-diag',
        title: 'n - n = 0',
        description: 'Prove the self-subtraction identity by induction.',
      },
      {
        problemSlug: 'even-odd-dec',
        title: 'Even or Odd',
        description: 'Prove every natural number is even or odd.',
      },
      {
        problemSlug: 'plus-assoc',
        title: 'Addition is Associative',
        description: 'A core arithmetic fact proved by induction.',
      },
      {
        problemSlug: 'mul-comm',
        title: 'Multiplication is Commutative',
        description: 'A challenging proof requiring multiple auxiliary lemmas.',
      },
    ],
  },

  /* ========================================================================
   * Advanced Paths
   * ===================================================================== */

  {
    slug: 'reasoning-about-data',
    title: 'Reasoning About Data',
    description: 'Prove properties about lists and trees. Learn structural induction on complex data types.',
    difficulty: 'advanced',
    icon: '🌳',
    steps: [
      {
        problemSlug: 'list-length-app',
        title: 'List Length and Append',
        description: 'Prove that length distributes over append.',
      },
      {
        problemSlug: 'tree-mirror',
        title: 'Mirror of Mirror',
        description: 'Induction on binary trees — prove mirror is an involution.',
      },
      {
        problemSlug: 'tree-size-node',
        title: 'Node Trees Have Positive Size',
        description: 'Combine tree induction with arithmetic.',
      },
      {
        problemSlug: 'list-rev-rev',
        title: 'Reverse of Reverse',
        description: 'A harder list induction requiring auxiliary lemmas.',
      },
      {
        problemSlug: 'bst-insert-member',
        title: 'BST Insert Contains Element',
        description: 'The hardest challenge — induction with case analysis on comparisons.',
      },
    ],
  },
  {
    slug: 'relations-and-equality',
    title: 'Relations & Equality',
    description: 'Prove properties about equality and ordering relations. Master the reflexive, symmetric, and transitive properties.',
    difficulty: 'advanced',
    icon: '⚖️',
    steps: [
      {
        problemSlug: 'eq-symmetry',
        title: 'Equality is Symmetric',
        description: 'Prove that if a = b then b = a.',
      },
      {
        problemSlug: 'eq-sym-trans',
        title: 'Symmetric Transitivity',
        description: 'Combine symmetry and transitivity of equality.',
      },
      {
        problemSlug: 'le-refl',
        title: 'Less-or-Equal is Reflexive',
        description: 'Prove n <= n for all natural numbers.',
      },
      {
        problemSlug: 'le-trans',
        title: 'Less-or-Equal is Transitive',
        description: 'Prove the transitive property of the ordering relation.',
      },
      {
        problemSlug: 'le-antisym',
        title: 'Less-or-Equal is Antisymmetric',
        description: 'Prove that n <= m and m <= n implies n = m.',
      },
    ],
  },
];
