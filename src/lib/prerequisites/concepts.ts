/**
 * Concept and tactic knowledge base for the prerequisite system.
 *
 * Defines the catalog of Coq concepts, tactics, and lemmas that problems can
 * declare as prerequisites. When a problem specifies prerequisites (in its JSON
 * definition), the prerequisite system looks up the concept IDs in this registry
 * to display helpful information and links.
 *
 * Each concept entry includes:
 * - A unique ID with a type prefix (e.g., 'tactic:intros', 'lemma:add_0_r')
 * - A human-readable display name and description
 * - A `learnPath` that either points to:
 *   - A tutorial section (URL starting with '/') where the concept is taught
 *   - A problem slug where the concept is first practiced
 *
 * The type prefix convention ('tactic:', 'lemma:', 'concept:') enables future
 * filtering and categorization in the UI.
 *
 * To add a new concept: append a `ConceptInfo` object to the `concepts` array.
 * It will automatically become available for use in problem prerequisite declarations.
 *
 * @module prerequisites/concepts
 */

/* ============================================================================
 * Type Definitions
 * ========================================================================= */

/**
 * Information about a single concept, tactic, or lemma.
 *
 * @property id - Unique identifier with type prefix (e.g., 'tactic:intros').
 *               This is the key used in problem prerequisite declarations.
 * @property type - Classification of the concept: 'tactic' for Coq proof tactics,
 *                  'lemma' for standard library lemmas, 'concept' for broader ideas.
 * @property displayName - Human-readable name shown in the prerequisites panel
 *                         (e.g., 'intros', 'Nat.add_0_r', 'Inductive types').
 * @property description - Brief explanation of what the concept is and when it is used.
 * @property learnPath - Where the user can learn about this concept. If it starts
 *                        with '/', it is a tutorial URL (e.g., '/tutorial#intros').
 *                        Otherwise, it is a problem slug (e.g., 'plus-n-zero')
 *                        whose completion satisfies this prerequisite.
 */
export interface ConceptInfo {
  id: string;
  type: 'tactic' | 'lemma' | 'concept';
  displayName: string;
  description: string;
  learnPath: string;
}

/* ============================================================================
 * Concept Registry
 * ========================================================================= */

/**
 * The complete catalog of concepts, tactics, and lemmas available for
 * prerequisite declarations.
 *
 * Organized into three sections:
 * 1. **Tactics**: Coq proof tactics (intros, apply, induction, etc.)
 * 2. **Lemmas**: Standard library lemmas commonly needed in proofs
 * 3. **Concepts**: Broader theoretical concepts (inductive types, etc.)
 */
export const concepts: ConceptInfo[] = [
  /* -- Tactics: Coq proof commands that users need to know -- */
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

  /* -- Lemmas: Standard library facts that problems may depend on -- */
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

  /* -- Concepts: Broader theoretical ideas -- */
  {
    id: 'concept:inductive-types',
    type: 'concept',
    displayName: 'Inductive types',
    description: 'Understanding Coq inductive type definitions like nat and list',
    learnPath: '/tutorial#inductive-types',
  },
];

/**
 * Pre-built lookup map from concept ID to its `ConceptInfo` object.
 *
 * Provides O(1) access to concept data by ID, used by `getPrerequisiteStatus()`
 * in `utils.ts` to resolve prerequisite concept IDs to their display info.
 */
export const conceptMap = new Map(concepts.map((c) => [c.id, c]));
