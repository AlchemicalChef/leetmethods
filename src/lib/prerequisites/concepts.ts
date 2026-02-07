export interface ConceptInfo {
  id: string;
  type: 'tactic' | 'lemma' | 'concept';
  displayName: string;
  description: string;
  learnPath: string; // tutorial step slug or problem slug
}

export const concepts: ConceptInfo[] = [
  // Tactics
  {
    id: 'tactic:intros',
    type: 'tactic',
    displayName: 'intros',
    description: 'Introduces hypotheses and variables into the proof context',
    learnPath: '/tutorial#intros',
  },
  {
    id: 'tactic:apply',
    type: 'tactic',
    displayName: 'apply',
    description: 'Applies a hypothesis or lemma to the current goal',
    learnPath: '/tutorial#apply',
  },
  {
    id: 'tactic:induction',
    type: 'tactic',
    displayName: 'induction',
    description: 'Performs structural induction on a variable',
    learnPath: '/tutorial#induction',
  },
  {
    id: 'tactic:destruct',
    type: 'tactic',
    displayName: 'destruct',
    description: 'Case analysis on a variable or hypothesis',
    learnPath: '/tutorial#destruct',
  },
  {
    id: 'tactic:rewrite',
    type: 'tactic',
    displayName: 'rewrite',
    description: 'Rewrites the goal using an equality hypothesis or lemma',
    learnPath: '/tutorial#rewrite',
  },
  {
    id: 'tactic:split',
    type: 'tactic',
    displayName: 'split',
    description: 'Splits a conjunction goal into two subgoals',
    learnPath: '/tutorial#split',
  },
  {
    id: 'tactic:exact',
    type: 'tactic',
    displayName: 'exact',
    description: 'Solves a goal when a hypothesis exactly matches',
    learnPath: '/tutorial#exact',
  },
  {
    id: 'tactic:simpl',
    type: 'tactic',
    displayName: 'simpl',
    description: 'Simplifies the goal using computation rules',
    learnPath: '/tutorial#simpl',
  },
  {
    id: 'tactic:reflexivity',
    type: 'tactic',
    displayName: 'reflexivity',
    description: 'Proves goals of the form x = x',
    learnPath: '/tutorial#reflexivity',
  },
  {
    id: 'tactic:lia',
    type: 'tactic',
    displayName: 'lia',
    description: 'Solves linear integer arithmetic goals automatically',
    learnPath: '/tutorial/applied-methods#lia',
  },
  // Lemmas
  {
    id: 'lemma:add_0_r',
    type: 'lemma',
    displayName: 'Nat.add_0_r',
    description: 'n + 0 = n, zero is right identity for addition',
    learnPath: 'plus-n-zero',
  },
  {
    id: 'lemma:add_succ_r',
    type: 'lemma',
    displayName: 'Nat.add_succ_r',
    description: 'n + S m = S (n + m)',
    learnPath: 'plus-comm',
  },
  {
    id: 'lemma:add_comm',
    type: 'lemma',
    displayName: 'Nat.add_comm',
    description: 'n + m = m + n, addition is commutative',
    learnPath: 'plus-comm',
  },
  {
    id: 'lemma:add_assoc',
    type: 'lemma',
    displayName: 'Nat.add_assoc',
    description: '(n + m) + p = n + (m + p), addition is associative',
    learnPath: 'plus-assoc',
  },
  // Concepts
  {
    id: 'concept:inductive-types',
    type: 'concept',
    displayName: 'Inductive types',
    description: 'Understanding Coq inductive type definitions like nat and list',
    learnPath: '/tutorial#inductive-types',
  },
];

export const conceptMap = new Map(concepts.map((c) => [c.id, c]));
