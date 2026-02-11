import type { TutorialStep } from './tutorial-steps';

export const logicNegationSteps: TutorialStep[] = [
  {
    id: 1,
    title: 'Negation and Contradiction',
    explanation: `In Coq, negation \`~P\` is defined as \`P -> False\`. This means "assuming P leads to a contradiction." To prove \`~P\`, you \`intros\` a proof of \`P\` and derive \`False\`.

**Double negation introduction** says: if \`P\` holds, then \`P\` cannot be refuted. In symbols: \`P -> ~~P\`, which unfolds to \`P -> (P -> False) -> False\`.

The key insight: if you have both \`HP : P\` and \`HnP : P -> False\`, you can \`apply HnP\` to reduce the goal \`False\` to \`P\`, then use \`exact HP\`.

**Your task:** Prove \`P -> ~~P\`. Introduce all three hypotheses (P, HP, and HnP), then derive the contradiction.`,
    exercise: {
      prelude: '(* No imports needed *)',
      template: `Theorem not_not_intro : forall P : Prop, P -> ~~P.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem not_not_intro : forall P : Prop, P -> ~~P.\nProof.\n  intros P HP HnP.\n  apply HnP.\n  exact HP.\nQed.`,
    },
    successMessage: 'You proved double negation introduction! The trick was recognizing that ~P is just P -> False, so you can apply it like any other implication.',
    hint: 'intros P HP HnP. apply HnP. exact HP.',
  },
  {
    id: 2,
    title: 'The left and right Tactics',
    explanation: `When the goal is a disjunction \`A \\/ B\`, you must choose which side to prove:

- \`left.\` changes the goal to \`A\`
- \`right.\` changes the goal to \`B\`

This is a commitment — once you choose a side, you must prove that side. Choose wisely based on what hypotheses you have available.

**Your task:** Prove \`P -> P \\/ Q\`. Since you have a proof of \`P\`, you should choose \`left\` to prove the left side of the disjunction.`,
    exercise: {
      prelude: '(* No imports needed *)',
      template: `Theorem or_intro_l : forall P Q : Prop, P -> P \\/ Q.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem or_intro_l : forall P Q : Prop, P -> P \\/ Q.\nProof.\n  intros P Q HP.\n  left.\n  exact HP.\nQed.`,
    },
    successMessage: 'You used "left" to commit to proving the left side of the disjunction. If you had a proof of Q instead, you would use "right".',
    hint: 'intros P Q HP. left. exact HP.',
  },
  {
    id: 3,
    title: 'The Contrapositive',
    explanation: `The **contrapositive** is a fundamental logical principle: if \`P -> Q\`, then \`~Q -> ~P\`. In other words, if P implies Q, then not-Q implies not-P.

Since \`~P\` unfolds to \`P -> False\`, after introducing all hypotheses you'll have:
- \`HPQ : P -> Q\`
- \`HnQ : Q -> False\` (this is \`~Q\`)
- \`HP : P\` (from unfolding \`~P\` in the goal)

And the goal will be \`False\`. Chain the implications: \`apply HnQ\` reduces \`False\` to \`Q\`, then \`apply HPQ\` reduces \`Q\` to \`P\`.

**Your task:** Prove the contrapositive by chaining \`apply\`.`,
    exercise: {
      prelude: '(* No imports needed *)',
      template: `Theorem contrapositive : forall P Q : Prop,\n  (P -> Q) -> ~Q -> ~P.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem contrapositive : forall P Q : Prop,\n  (P -> Q) -> ~Q -> ~P.\nProof.\n  intros P Q HPQ HnQ HP.\n  apply HnQ.\n  apply HPQ.\n  exact HP.\nQed.`,
    },
    successMessage: 'You chained implications backwards: apply HnQ reduced False to Q, apply HPQ reduced Q to P, and exact HP closed the proof. This backward-chaining style is very common in Coq.',
    hint: 'intros P Q HPQ HnQ HP. apply HnQ. apply HPQ. exact HP.',
  },
  {
    id: 4,
    title: 'Working with Iff',
    explanation: `Logical equivalence \`P <-> Q\` is defined as \`(P -> Q) /\\ (Q -> P)\` — a conjunction of two implications.

**To prove \`P <-> Q\`:** Use \`split\` to get two subgoals, one for each direction.

**To use \`H : P <-> Q\`:** Use \`destruct H as [HPQ HQP]\` to extract both directions as separate hypotheses.

**Your task:** Prove that iff is symmetric: \`(P <-> Q) -> (Q <-> P)\`. Destruct the hypothesis to get both directions, then split and provide them in the opposite order.`,
    exercise: {
      prelude: '(* No imports needed *)',
      template: `Theorem iff_sym : forall P Q : Prop,\n  (P <-> Q) -> (Q <-> P).\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem iff_sym : forall P Q : Prop,\n  (P <-> Q) -> (Q <-> P).\nProof.\n  intros P Q H.\n  destruct H as [HPQ HQP].\n  split.\n  - exact HQP.\n  - exact HPQ.\nQed.`,
    },
    successMessage: 'You decomposed the iff into its two directions and reassembled them swapped. The pattern destruct + split is the standard way to manipulate iff.',
    hint: 'intros P Q H. destruct H as [HPQ HQP]. split. - exact HQP. - exact HPQ.',
  },
  {
    id: 5,
    title: 'The discriminate Tactic',
    explanation: `In Coq, different constructors of an inductive type are always distinct. For booleans, \`true <> false\` (they are not equal). The notation \`x <> y\` unfolds to \`x = y -> False\`.

**\`discriminate\`** proves goals of the form \`H : c1 ... = c2 ...\` where \`c1\` and \`c2\` are different constructors. It recognizes that such an equality is impossible and immediately closes the goal with \`False\`.

**Your task:** Prove \`true <> false\`. After introducing the equality hypothesis, use \`discriminate\` to derive the contradiction.`,
    exercise: {
      prelude: 'Require Import Bool.',
      template: `Theorem true_neq_false : true <> false.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem true_neq_false : true <> false.\nProof.\n  intros H.\n  discriminate H.\nQed.`,
    },
    successMessage: 'The discriminate tactic recognized that true and false are different constructors, making the equality hypothesis contradictory. This works for any two distinct constructors (e.g., O <> S n, nil <> cons x l).',
    hint: 'intros H. discriminate H.',
  },
  {
    id: 6,
    title: 'Putting It Together',
    explanation: `Let's combine everything from this tutorial. You'll need \`destruct\` to decompose iff, \`split\` to build iff, and \`intros\`/\`exact\`/\`apply\` to handle the implications.

**Your task:** Prove that if \`P <-> Q\`, then \`Q <-> P\` (with an extra twist — prove it using a slightly different structure that exercises more tactics).

Actually, let's prove something more involved: \`(P <-> Q) -> (~P <-> ~Q)\`. If P and Q are equivalent, then their negations are also equivalent.

Remember: \`~P\` is \`P -> False\`, so you'll need to chain implications carefully in each direction.`,
    exercise: {
      prelude: '(* No imports needed *)',
      template: `Theorem iff_neg : forall P Q : Prop,\n  (P <-> Q) -> (~P <-> ~Q).\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem iff_neg : forall P Q : Prop,\n  (P <-> Q) -> (~P <-> ~Q).\nProof.\n  intros P Q H.\n  destruct H as [HPQ HQP].\n  split.\n  - intros HnP HQ. apply HnP. apply HQP. exact HQ.\n  - intros HnQ HP. apply HnQ. apply HPQ. exact HP.\nQed.`,
    },
    successMessage: 'Excellent! You proved that logical equivalence preserves negation, combining destruct, split, intros, and apply. You now have a solid foundation in propositional logic. Next up: Proof Strategies!',
    hint: 'intros P Q H. destruct H as [HPQ HQP]. split. - intros HnP HQ. apply HnP. apply HQP. exact HQ. - intros HnQ HP. apply HnQ. apply HPQ. exact HP.',
  },
];
