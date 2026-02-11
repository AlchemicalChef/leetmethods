import type { TutorialStep } from './tutorial-steps';

export const proofStrategiesSteps: TutorialStep[] = [
  {
    id: 1,
    title: 'The f_equal Tactic',
    explanation: `**\`f_equal\`** proves goals of the form \`f a1 ... = f a1' ...\` by reducing them to \`a1 = a1'\`, \`a2 = a2'\`, etc. In other words, if two expressions have the same outer function, it suffices to show the arguments are equal.

For natural numbers, this is especially useful: to prove \`S n = S m\`, \`f_equal\` reduces the goal to \`n = m\`.

You can also use \`f_equal\` as a manual alternative to \`rewrite\` when you want to "peel off" a constructor.

**Your task:** Prove that if \`n = m\`, then \`S n = S m\`. Introduce the hypothesis, then use \`f_equal\` to strip the \`S\` constructor.`,
    exercise: {
      prelude: '(* No imports needed *)',
      template: `Theorem succ_eq : forall n m : nat,\n  n = m -> S n = S m.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem succ_eq : forall n m : nat,\n  n = m -> S n = S m.\nProof.\n  intros n m H.\n  f_equal.\n  exact H.\nQed.`,
    },
    successMessage: 'f_equal stripped the S constructor from both sides, reducing "S n = S m" to "n = m". This works for any function application, not just constructors.',
    hint: 'intros n m H. f_equal. exact H.',
  },
  {
    id: 2,
    title: 'The assert Tactic',
    explanation: `**\`assert\`** lets you state and prove intermediate lemmas inside a proof. This is like saying "first, let me establish this fact, then I'll use it."

\`assert (H : P).\` creates two subgoals:
1. Prove \`P\` (the asserted claim)
2. Continue the original proof with \`H : P\` as a new hypothesis

This is invaluable when a proof requires an intermediate result. You can also use the inline form: \`assert (H : P) by tactic.\`

**Your task:** Prove that \`n + 0 = 0 + n\` by asserting the intermediate fact \`n + 0 = n\` (which requires induction), then using rewrite. For this exercise, we'll use a simpler version that can be solved with \`assert\` and basic tactics.`,
    exercise: {
      prelude: 'Require Import Arith.\nRequire Import Lia.',
      template: `Theorem add_comm_zero : forall n : nat,\n  n + 0 = 0 + n.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem add_comm_zero : forall n : nat,\n  n + 0 = 0 + n.\nProof.\n  intros n.\n  assert (H : n + 0 = n).\n  { lia. }\n  rewrite H.\n  simpl.\n  reflexivity.\nQed.`,
    },
    successMessage: 'You used assert to establish n + 0 = n as an intermediate fact, then rewrote with it. The assert tactic is essential for structuring complex proofs into manageable pieces.',
    hint: 'intros n. assert (H : n + 0 = n). { lia. } rewrite H. simpl. reflexivity.',
  },
  {
    id: 3,
    title: 'Rewriting in Hypotheses',
    explanation: `You already know \`rewrite H\` changes the **goal**. But sometimes you need to rewrite inside a **hypothesis** instead.

**\`rewrite H1 in H2.\`** replaces occurrences of the left-hand side of \`H1\` with the right-hand side, but inside hypothesis \`H2\` rather than the goal.

**\`rewrite <- H1 in H2.\`** rewrites in the reverse direction within \`H2\`.

This is useful when you need to transform a hypothesis to match what another tactic expects.

**Your task:** Given \`n = m\` and \`n + p = 0\`, prove \`m + p = 0\`. Rewrite the first equality **in** the second hypothesis using \`rewrite Heq in Hsum\`, then use \`exact\`.`,
    exercise: {
      prelude: '(* No imports needed *)',
      template: `Theorem rewrite_in_hyp : forall n m p : nat,\n  n = m -> n + p = 0 -> m + p = 0.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem rewrite_in_hyp : forall n m p : nat,\n  n = m -> n + p = 0 -> m + p = 0.\nProof.\n  intros n m p Heq Hsum.\n  rewrite Heq in Hsum.\n  exact Hsum.\nQed.`,
    },
    successMessage: 'You used "rewrite Heq in Hsum" to substitute n with m inside the hypothesis, making it exactly match the goal. You could also have used "rewrite <- Heq" to rewrite the goal instead.',
    hint: 'intros n m p Heq Hsum. rewrite Heq in Hsum. exact Hsum.',
  },
  {
    id: 4,
    title: 'Bullet Points and Structure',
    explanation: `When a tactic creates multiple subgoals (like \`split\`, \`destruct\`, or \`induction\`), you should **structure** your proof with bullet points:

- \`-\` for the first level of subgoals
- \`+\` for nested subgoals within a \`-\` branch
- \`*\` for a third nesting level

Bullets make proofs **much** more readable and help Coq catch mistakes — if you accidentally prove the wrong subgoal, Coq will tell you.

**Your task:** Prove \`P /\\ Q -> Q /\\ P\` using bullet points to clearly separate the two subgoals after \`split\`.`,
    exercise: {
      prelude: '(* No imports needed *)',
      template: `Theorem and_comm : forall P Q : Prop,\n  P /\\ Q -> Q /\\ P.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem and_comm : forall P Q : Prop,\n  P /\\ Q -> Q /\\ P.\nProof.\n  intros P Q H.\n  destruct H as [HP HQ].\n  split.\n  - exact HQ.\n  - exact HP.\nQed.`,
    },
    successMessage: 'Clean and structured! The bullet points make it immediately clear which subgoal each tactic addresses. Always use bullets in proofs with multiple subgoals.',
    hint: 'intros P Q H. destruct H as [HP HQ]. split. - exact HQ. - exact HP.',
  },
  {
    id: 5,
    title: 'The auto and trivial Tactics',
    explanation: `Coq has built-in automation tactics that can solve simple goals without manual work:

**\`trivial\`** — Solves very simple goals: hypotheses that directly match the goal, \`reflexivity\`, etc.

**\`auto\`** — More powerful than \`trivial\`. It searches for proofs by combining \`intros\`, \`apply\`, \`split\`, \`left\`, \`right\`, and hypotheses. It can chain several steps automatically.

**\`auto\` will never fail** — if it can't prove the goal, it just leaves it unchanged (unlike \`exact\` which gives an error). This makes it safe to try.

**When to use automation:** Use \`auto\` for "obvious" subgoals in larger proofs. Don't rely on it for everything — understanding the manual tactics is essential.

**Your task:** Prove a multi-step logical statement using \`auto\`. Try solving it both manually and with \`auto\` to see the difference.`,
    exercise: {
      prelude: '(* No imports needed *)',
      template: `Theorem auto_demo : forall P Q R : Prop,\n  (P -> Q) -> (Q -> R) -> P -> R.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem auto_demo : forall P Q R : Prop,\n  (P -> Q) -> (Q -> R) -> P -> R.\nProof.\n  auto.\nQed.`,
    },
    successMessage: 'auto solved the whole thing in one step! It figured out the chain: intros, apply the Q -> R hypothesis, apply the P -> Q hypothesis, use the P hypothesis. For simple logic, auto is very effective.',
    hint: 'auto. (That\'s it! auto handles this entire proof automatically.)',
  },
  {
    id: 6,
    title: 'Strategy Recap',
    explanation: `Let's put everything together with a proof that requires multiple techniques. You'll need:

- **\`induction\`** to prove a property about natural numbers
- **\`simpl\`** to reduce computations
- **\`rewrite\`** to use the induction hypothesis
- **Bullet points** to structure subgoals
- Good **proof strategy**: read the goal, choose the right tactic

**Your task:** Prove that \`n + S m = S (n + m)\`. This is a fundamental property of addition that requires induction on \`n\`. In the base case, \`simpl\` suffices. In the inductive step, \`simpl\` followed by \`rewrite\` with the IH does the job.`,
    exercise: {
      prelude: 'Require Import Arith.',
      template: `Theorem plus_n_Sm : forall n m : nat,\n  n + S m = S (n + m).\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem plus_n_Sm : forall n m : nat,\n  n + S m = S (n + m).\nProof.\n  intros n m.\n  induction n as [| n' IHn'].\n  - simpl. reflexivity.\n  - simpl. rewrite IHn'. reflexivity.\nQed.`,
    },
    successMessage: 'Congratulations! You\'ve completed the Proof Strategies tutorial! You now have a strong foundation in Coq tactics: intros, exact, apply, split, destruct, left/right, rewrite, induction, simpl, reflexivity, f_equal, assert, discriminate, auto, and proof structuring. Continue to Polymorphism to learn about generic types and higher-order functions!',
    hint: 'intros n m. induction n as [| n\' IHn\']. - simpl. reflexivity. - simpl. rewrite IHn\'. reflexivity.',
  },
];
