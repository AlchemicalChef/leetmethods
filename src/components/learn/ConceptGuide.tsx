/**
 * @module ConceptGuide
 *
 * Expandable accordion of core Coq concepts with explanations and code examples.
 *
 * This component provides educational content for users learning Coq, covering
 * fundamental topics like propositions, induction, lists, relations, and
 * data structures. Each concept can be expanded to reveal a prose explanation
 * and an optional Coq code example.
 *
 * The concept data is defined inline as a static array rather than loaded
 * from files because:
 *   1. The content is short and unlikely to change frequently
 *   2. Keeping it co-located with the component makes it easy to update
 *   3. No build pipeline or content management is needed
 *
 * Design decisions:
 *   - Only one concept can be expanded at a time (accordion pattern) to
 *     keep the page scannable and reduce cognitive overload.
 *   - Examples use `<pre><code>` blocks with monospace font for proper
 *     Coq code formatting, including inline comments.
 *   - The chevron icon rotates between right (collapsed) and down (expanded)
 *     to give clear visual feedback about the expandable state.
 */
'use client';

import { useState } from 'react';
import { Card } from '@/components/ui/card';
import { ChevronDown, ChevronRight } from 'lucide-react';

/* ========================================================================
 * Concept Data Definitions
 * ======================================================================== */

/**
 * Shape of a single concept section in the guide.
 *
 * @property title - Display name shown in the accordion header.
 * @property content - Prose explanation of the concept.
 * @property example - Optional Coq code example demonstrating the concept.
 */
interface ConceptSection {
  title: string;
  content: string;
  example?: string;
}

/**
 * Static array of concept sections covering the core topics taught in
 * LeetMethods. Each entry maps to one expandable accordion item.
 *
 * The ordering is intentional: starts with the foundational Curry-Howard
 * correspondence, then builds up through induction, lists, relations,
 * and custom data structures -- mirroring the typical learning progression.
 */
const concepts: ConceptSection[] = [
  {
    title: 'Propositions and Proofs',
    content:
      'In Coq, propositions are types and proofs are programs. A proposition P : Prop is proven by constructing a term of type P. The Curry-Howard correspondence connects logical connectives to type constructors: implications are functions, conjunctions are pairs, and disjunctions are tagged unions.',
    example: `(* P -> Q means: given a proof of P, produce a proof of Q *)
Theorem impl_example : forall P Q : Prop, P -> (P -> Q) -> Q.
Proof.
  intros P Q HP HPQ.
  apply HPQ. exact HP.
Qed.`,
  },
  {
    title: 'Induction',
    content:
      "Proof by induction is how we prove properties of recursively defined types like nat and list. For natural numbers, you prove a base case (n = 0) and a step case (assuming the property for n, prove it for S n). Coq's `induction` tactic generates both subgoals automatically.",
    example: `Theorem plus_0_r : forall n : nat, n + 0 = n.
Proof.
  induction n as [| n' IHn'].
  - (* Base case: 0 + 0 = 0 *)
    simpl. reflexivity.
  - (* Step case: S n' + 0 = S n' *)
    simpl. rewrite IHn'. reflexivity.
Qed.`,
  },
  {
    title: 'Working with Lists',
    content:
      'Lists in Coq are inductively defined as either nil (empty) or cons (an element followed by a list). Properties of list operations like append (++), length, and reverse are proven by induction on the list structure. The key is understanding how each operation unfolds on nil vs cons.',
    example: `(* List append is associative *)
Theorem app_assoc : forall (A : Type) (l m n : list A),
  l ++ (m ++ n) = (l ++ m) ++ n.
Proof.
  intros A l m n.
  induction l as [| a l' IHl'].
  - simpl. reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.`,
  },
  {
    title: 'Relations and Orderings',
    content:
      "Relations in Coq are defined as propositions over pairs of values. The less-than-or-equal relation (le) on natural numbers is defined inductively: n <= n (reflexivity) and n <= m implies n <= S m. Properties like transitivity and antisymmetry can be proven using induction on the relation's structure.",
    example: `(* le is reflexive *)
Theorem le_refl : forall n : nat, n <= n.
Proof.
  intro n. apply le_n.
Qed.`,
  },
  {
    title: 'Data Structures',
    content:
      'Custom inductive types like binary trees let you model complex data structures in Coq. You define the type with constructors (Leaf, Node), write recursive functions over them (mirror, size), and prove properties using structural induction — the same pattern as with nat and list, but with multiple recursive cases.',
    example: `(* A binary tree *)
Inductive tree (A : Type) : Type :=
  | Leaf : tree A
  | Node : A -> tree A -> tree A -> tree A.

(* Size counts all nodes *)
Fixpoint size {A : Type} (t : tree A) : nat :=
  match t with
  | Leaf _ => 0
  | Node _ _ l r => 1 + size l + size r
  end.`,
  },
];

/* ========================================================================
 * ConceptGuide Component
 * ======================================================================== */

/**
 * Renders an accordion-style list of Coq concept explanations with
 * optional code examples.
 *
 * @returns The concept guide accordion UI.
 */
export function ConceptGuide() {
  /** Title of the currently expanded concept, or null if all are collapsed */
  const [expanded, setExpanded] = useState<string | null>(null);

  return (
    <div className="space-y-2">
      {concepts.map((concept) => (
        <Card key={concept.title} className="overflow-hidden">
          {/* Accordion header -- clickable button that toggles expansion.
              Clicking an already-expanded concept collapses it. */}
          <button
            onClick={() => setExpanded(expanded === concept.title ? null : concept.title)}
            className="w-full p-4 flex items-center gap-3 hover:bg-muted/30 transition-colors text-left"
          >
            {/* Chevron direction indicates expanded/collapsed state */}
            {expanded === concept.title ? (
              <ChevronDown className="h-4 w-4 shrink-0" />
            ) : (
              <ChevronRight className="h-4 w-4 shrink-0" />
            )}
            <span className="font-medium">{concept.title}</span>
          </button>

          {/* Expanded content area -- only rendered for the active concept */}
          {expanded === concept.title && (
            <div className="border-t px-4 py-4 space-y-4 bg-muted/10">
              {/* Prose explanation of the concept */}
              <p className="text-sm leading-relaxed">{concept.content}</p>

              {/* Optional Coq code example in a scrollable monospace block */}
              {concept.example && (
                <pre className="text-sm font-mono bg-muted p-4 rounded-md overflow-x-auto">
                  <code>{concept.example}</code>
                </pre>
              )}
            </div>
          )}
        </Card>
      ))}
    </div>
  );
}
