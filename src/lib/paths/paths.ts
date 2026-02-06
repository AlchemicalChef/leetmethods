import type { LearningPath } from './types';

export const learningPaths: LearningPath[] = [
  {
    slug: 'foundations-of-logic',
    title: 'Foundations of Logic',
    description: 'Master the basics of propositional logic in Coq. Learn intros, apply, exact, and how to work with implications and conjunctions.',
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
        title: 'Double Negation',
        description: 'Work with negation and learn how contradiction helps.',
      },
      {
        problemSlug: 'and-commutative',
        title: 'And is Commutative',
        description: 'Use split, destruct, and left/right to work with conjunctions.',
      },
      {
        problemSlug: 'le-refl',
        title: 'Less-or-Equal is Reflexive',
        description: 'Apply what you learned to a simple property of relations.',
      },
    ],
  },
  {
    slug: 'mastering-induction',
    title: 'Mastering Induction',
    description: 'Learn proof by induction on natural numbers. Progress from simple base-step proofs to multi-variable induction.',
    difficulty: 'intermediate',
    icon: '🔄',
    steps: [
      {
        problemSlug: 'plus-n-zero',
        title: 'n + 0 = n',
        description: 'Your first induction proof — the classic base case + inductive step.',
      },
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
        problemSlug: 'add-assoc',
        title: 'Addition is Associative',
        description: 'Prove associativity with careful induction.',
      },
    ],
  },
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
];
