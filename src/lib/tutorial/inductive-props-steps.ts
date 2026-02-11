import type { TutorialStep } from './types';

const evPrelude = `Inductive my_even : nat -> Prop :=
  | my_even_O : my_even 0
  | my_even_SS : forall n, my_even n -> my_even (S (S n)).`;

const lePrelude = `Inductive my_le : nat -> nat -> Prop :=
  | my_le_n : forall n, my_le n n
  | my_le_S : forall n m, my_le n m -> my_le n (S m).`;

export const inductivePropsSteps: TutorialStep[] = [
  {
    id: 1,
    title: 'Inductive Propositions: Even Numbers',
    explanation: `So far you've seen inductive *data types* like \`nat\` and \`list\`. Coq also lets you define inductive **propositions** — types in \`Prop\` whose constructors represent *evidence* or *proof rules*.

The classic example is "evenness." Instead of a boolean function \`even : nat -> bool\`, we define a *proposition* \`my_even : nat -> Prop\` inductively:

- \`my_even_O : my_even 0\` — zero is even (base case)
- \`my_even_SS : forall n, my_even n -> my_even (S (S n))\` — if n is even, so is n+2

To prove \`my_even 4\`, you build evidence: \`my_even_SS 2 (my_even_SS 0 my_even_O)\`.

**Your task:** Prove that 4 is even by applying the constructors. Use \`apply my_even_SS\` twice, then \`apply my_even_O\`.`,
    exercise: {
      prelude: evPrelude,
      template: `Theorem four_is_even : my_even 4.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem four_is_even : my_even 4.\nProof.\n  apply my_even_SS.\n  apply my_even_SS.\n  apply my_even_O.\nQed.`,
    },
    successMessage: 'You built evidence of evenness by chaining constructors: 4 is even because 2 is even (my_even_SS), and 2 is even because 0 is even (my_even_SS, my_even_O). This is fundamentally different from computing a boolean — you\'re constructing a proof object.',
    hint: 'apply my_even_SS. apply my_even_SS. apply my_even_O.',
  },
  {
    id: 2,
    title: 'Analyzing Evidence with inversion',
    explanation: `When you have a hypothesis like \`H : my_even (S (S n))\`, you know it *must* have been built using \`my_even_SS\`. The **\`inversion\`** tactic formalizes this reasoning: it looks at which constructors could have produced the evidence and extracts the underlying facts.

\`inversion H\` on \`H : my_even (S (S n))\` will:
1. Determine that only \`my_even_SS\` could produce this
2. Give you a new hypothesis \`my_even n\`
3. Add equalities that you can clear with \`subst\`

For \`H : my_even 1\`, \`inversion H\` would produce **no subgoals** because no constructor can build evidence of \`my_even 1\` — this proves the goal by contradiction.

**Your task:** Prove that if \`S (S n)\` is even, then \`n\` is even. Use \`inversion\` to extract the underlying evidence.`,
    exercise: {
      prelude: evPrelude,
      template: `Theorem even_SS_inv : forall n,\n  my_even (S (S n)) -> my_even n.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem even_SS_inv : forall n,\n  my_even (S (S n)) -> my_even n.\nProof.\n  intros n H.\n  inversion H.\n  assumption.\nQed.`,
    },
    successMessage: 'inversion analyzed the evidence for my_even (S (S n)) and determined it must have come from my_even_SS, giving you a proof of my_even n. This is the inductive proposition analog of "destruct" for data types.',
    hint: 'intros n H. inversion H. assumption.',
  },
  {
    id: 3,
    title: 'Impossibility by Inversion',
    explanation: `One of the most powerful uses of \`inversion\` is proving **impossibility**. If you have evidence that something is true, but no constructor could have produced it, then you have a contradiction.

For example, \`my_even 1\` is impossible: \`my_even_O\` produces \`my_even 0\` (not 1), and \`my_even_SS\` produces \`my_even (S (S n))\` which has the form 2, 4, 6, ... (not 1). So \`inversion\` on \`H : my_even 1\` solves the goal immediately.

This is similar to \`discriminate\` for data (which proves \`true <> false\`), but \`inversion\` works for propositions.

**Your task:** Prove that 1 is not even. Remember that \`~P\` unfolds to \`P -> False\`, so introduce the evidence for \`my_even 1\`, then use \`inversion\` to derive a contradiction.`,
    exercise: {
      prelude: evPrelude,
      template: `Theorem one_not_even : ~ my_even 1.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem one_not_even : ~ my_even 1.\nProof.\n  intros H.\n  inversion H.\nQed.`,
    },
    successMessage: 'inversion found that no constructor of my_even can produce my_even 1, so the hypothesis is contradictory. This closed the goal immediately — no need to explicitly derive False.',
    hint: 'intros H. inversion H.',
  },
  {
    id: 4,
    title: 'Induction on Evidence',
    explanation: `Just as you can do induction on \`nat\` (base: 0, step: S n) or \`list\` (base: nil, step: cons), you can do **induction on evidence** of an inductive proposition.

For \`my_even\`, \`induction H\` creates two subgoals matching the constructors:
- **my_even_O case:** prove the property for \`my_even 0\`
- **my_even_SS case:** given \`my_even n\` and the IH, prove for \`my_even (S (S n))\`

This is more powerful than induction on \`n\` because it only considers even numbers.

**Your task:** Prove that for any even number \`n\`, there exists an \`m\` such that \`n = m + m\` (i.e., even numbers are doubles). Use induction on the evidence \`H : my_even n\`.`,
    exercise: {
      prelude: `Require Import Arith.\n\n${evPrelude}`,
      template: `Theorem even_is_double : forall n,\n  my_even n -> exists m, n = m + m.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem even_is_double : forall n,\n  my_even n -> exists m, n = m + m.\nProof.\n  intros n H.\n  induction H.\n  - exists 0. reflexivity.\n  - destruct IHmy_even as [m Hm].\n    exists (S m). rewrite Hm. simpl. rewrite <- plus_n_Sm. reflexivity.\nQed.`,
    },
    successMessage: 'You performed induction on evidence! In the base case, 0 = 0 + 0. In the step, if n = m + m, then S (S n) = S m + S m. The key was using "induction H" instead of "induction n" to follow the structure of the evidence.',
    hint: 'induction H. - exists 0. reflexivity. - destruct IHmy_even as [m Hm]. exists (S m). rewrite Hm. simpl. rewrite <- plus_n_Sm. reflexivity.',
  },
  {
    id: 5,
    title: 'Inductive Relations: Less-Than-or-Equal',
    explanation: `Inductive propositions can relate two values. A classic example is **less-than-or-equal** on natural numbers:

- \`my_le_n : forall n, my_le n n\` — every number is <= itself (reflexivity)
- \`my_le_S : forall n m, my_le n m -> my_le n (S m)\` — if n <= m, then n <= S m

So \`my_le 2 4\` is proved by: \`my_le_S 2 3 (my_le_S 2 2 (my_le_n 2))\`.

This is how Coq's standard \`le\` is defined. The idea is that to go from \`n <= n\` to \`n <= n+k\`, you apply \`my_le_S\` exactly \`k\` times.

**Your task:** Prove that 2 <= 4 using the constructors. Apply \`my_le_S\` twice, then \`my_le_n\`.`,
    exercise: {
      prelude: lePrelude,
      template: `Theorem le_2_4 : my_le 2 4.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem le_2_4 : my_le 2 4.\nProof.\n  apply my_le_S.\n  apply my_le_S.\n  apply my_le_n.\nQed.`,
    },
    successMessage: 'You constructed evidence of 2 <= 4 by starting at 2 <= 2 (reflexivity) and applying my_le_S twice to reach 2 <= 4. Binary inductive relations like this are the foundation for reasoning about program behavior in later tutorials.',
    hint: 'apply my_le_S. apply my_le_S. apply my_le_n.',
  },
  {
    id: 6,
    title: 'Proving Transitivity',
    explanation: `Let's prove a fundamental property: **transitivity** of \`my_le\`. If \`a <= b\` and \`b <= c\`, then \`a <= c\`.

The key strategy: **induct on the second evidence** \`H2 : my_le b c\`. Why? Because \`my_le\` is defined by adding \`S\` on the right:
- If \`H2\` is \`my_le_n\` (so \`b = c\`), then \`my_le a b\` immediately gives \`my_le a c\`.
- If \`H2\` is \`my_le_S\` (so \`c = S c'\` with \`my_le b c'\`), the IH gives \`my_le a c'\`, and one \`my_le_S\` gives \`my_le a (S c')\`.

**Your task:** Prove transitivity. Induct on \`H2\` and use \`apply\` with the constructors and IH.`,
    exercise: {
      prelude: lePrelude,
      template: `Theorem my_le_trans : forall a b c,\n  my_le a b -> my_le b c -> my_le a c.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem my_le_trans : forall a b c,\n  my_le a b -> my_le b c -> my_le a c.\nProof.\n  intros a b c H1 H2.\n  induction H2.\n  - exact H1.\n  - apply my_le_S. apply IHmy_le. exact H1.\nQed.`,
    },
    successMessage: 'Excellent! You proved transitivity by inducting on the second evidence. This pattern — inducting on the "right" evidence for le-style relations — appears throughout program verification. You\'ve now mastered inductive propositions, the foundation for defining language semantics and type systems!',
    hint: 'intros a b c H1 H2. induction H2. - exact H1. - apply my_le_S. apply IHmy_le. exact H1.',
  },
];
