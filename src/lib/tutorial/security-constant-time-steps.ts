/**
 * @module security-constant-time-steps
 *
 * Tutorial steps for "Constant-Time Programming" — the third tutorial in
 * the Security Foundations (SecF) volume group.
 *
 * Based on Software Foundations Volume 7, Chapter 4 (SpecCT). This tutorial
 * introduces the concept of constant-time programming: ensuring that a
 * program's observable behavior (branch patterns, memory access patterns,
 * execution time) does not depend on secret inputs.
 *
 * Side-channel attacks exploit observable differences to extract secrets.
 * Constant-time programming is the primary defense, used in all modern
 * cryptographic libraries.
 *
 * Concepts covered:
 *   1. Observations and distinguishability
 *   2. The constant-time property definition
 *   3. Proving a function violates constant-time
 *   4. Composition of constant-time functions
 *   5. Timing leak detection
 *   6. Balanced branches as a defense
 *
 * Tactics introduced/reinforced:
 *   - discriminate, unfold, intros, reflexivity, intro, specialize,
 *     simpl in, rewrite, destruct
 */
import type { TutorialStep } from './types';

export const securityConstantTimeSteps: TutorialStep[] = [
  /* ------------------------------------------------------------------
   * Step 1: What Attackers Observe
   * ------------------------------------------------------------------ */
  {
    id: 1,
    title: 'What Attackers Observe',
    explanation: `Side-channel attacks work by observing a program's **behavior**, not its output. An attacker might measure:

- **Branch direction**: Did the program take the \`then\` or \`else\` branch?
- **Memory access pattern**: Which array index was accessed?
- **Execution time**: How long did the computation take?

We model these as an \`observation\` type:
\`\`\`
Inductive observation : Type :=
  | Branch : bool -> observation
  | Access : nat -> observation
  | Silent : observation.
\`\`\`

If two observations differ, the attacker can distinguish them. Prove that taking the \`true\` branch is distinguishable from taking the \`false\` branch.`,
    exercise: {
      prelude: `Inductive observation : Type :=
  | Branch : bool -> observation
  | Access : nat -> observation
  | Silent : observation.`,
      template: `Theorem diff_branches_distinguishable :
  Branch true <> Branch false.
Proof.
  (* These are different constructor applications *)
Admitted.`,
      solution: `Theorem diff_branches_distinguishable :
  Branch true <> Branch false.
Proof.
  discriminate.
Qed.`,
    },
    hint: 'Use `discriminate` — it proves inequality when the constructor arguments differ (`true` vs `false`).',
    successMessage: 'Different branch directions produce distinguishable observations — this is exactly what side-channel attackers exploit!',
  },

  /* ------------------------------------------------------------------
   * Step 2: The Constant-Time Property
   * ------------------------------------------------------------------ */
  {
    id: 2,
    title: 'The Constant-Time Property',
    explanation: `A program is **constant-time** if its observable behavior is the same regardless of secret input. We model a program as a function from secret input to an observation:

\`\`\`
Definition constant_time (observe : nat -> nat) : Prop :=
  forall s1 s2 : nat, observe s1 = observe s2.
\`\`\`

The simplest constant-time program ignores the secret entirely, always producing the same observation (modeled here as always returning 0).

Use \`unfold\` to expand the definition, \`intros\` to name variables, and \`reflexivity\` to close the goal.`,
    exercise: {
      prelude: `Definition constant_time (observe : nat -> nat) : Prop :=
  forall s1 s2 : nat, observe s1 = observe s2.`,
      template: `Theorem ignore_secret_ct :
  constant_time (fun _ => 0).
Proof.
  (* Unfold and prove the observations are equal *)
Admitted.`,
      solution: `Theorem ignore_secret_ct :
  constant_time (fun _ => 0).
Proof.
  unfold constant_time.
  intros s1 s2.
  reflexivity.
Qed.`,
    },
    hint: 'Use `unfold constant_time. intros s1 s2. reflexivity.` — the function ignores its argument, so both sides are identical.',
    successMessage: 'A function that ignores the secret is trivially constant-time — no information can leak if the secret is never used!',
  },

  /* ------------------------------------------------------------------
   * Step 3: Branching on Secrets Leaks
   * ------------------------------------------------------------------ */
  {
    id: 3,
    title: 'Branching on Secrets Leaks',
    explanation: `The most common constant-time violation: **branching on a secret value**. Consider:

\`\`\`
Definition leaky_branch (secret : bool) : nat :=
  if secret then 1 else 0.
\`\`\`

This is NOT constant-time — the observation (1 or 0) reveals the secret. To prove \`~ constant_time_bool leaky_branch\`:

1. \`unfold\` both definitions
2. \`intro H\` to assume it IS constant-time (we'll derive a contradiction)
3. \`specialize (H true false)\` to instantiate with revealing inputs
4. \`simpl in H\` to compute: \`1 = 0\`
5. \`discriminate H\` to derive contradiction from \`1 = 0\``,
    exercise: {
      prelude: `Definition constant_time_bool (observe : bool -> nat) : Prop :=
  forall s1 s2 : bool, observe s1 = observe s2.

Definition leaky_branch (secret : bool) : nat :=
  if secret then 1 else 0.`,
      template: `Theorem leaky_not_ct : ~ constant_time_bool leaky_branch.
Proof.
  (* Assume CT holds, find a contradiction *)
Admitted.`,
      solution: `Theorem leaky_not_ct : ~ constant_time_bool leaky_branch.
Proof.
  unfold constant_time_bool, leaky_branch.
  intro H.
  specialize (H true false).
  simpl in H.
  discriminate H.
Qed.`,
    },
    hint: 'After `unfold constant_time_bool, leaky_branch. intro H.`, use `specialize (H true false).` to get `H : 1 = 0`. Then `simpl in H. discriminate H.` finishes the proof.',
    successMessage: 'You proved that branching on a secret leaks information! This is the #1 rule of constant-time programming: never branch on secret data.',
  },

  /* ------------------------------------------------------------------
   * Step 4: Composition Preserves Security
   * ------------------------------------------------------------------ */
  {
    id: 4,
    title: 'Composition Preserves Security',
    explanation: `An important property: if two functions are individually constant-time, their **composition** is also constant-time. This lets us build secure systems from verified building blocks.

If \`f\` is constant-time (\`f s1 = f s2\` for all secrets) and \`g\` is constant-time, then \`fun x => g (f x)\` is constant-time.

The key insight: since \`f s1 = f s2\`, we can \`rewrite\` one into the other, making both sides of the composed equation identical.

Use \`rewrite (Hf s1 s2)\` to replace \`f s1\` with \`f s2\` in the goal.`,
    exercise: {
      prelude: `Definition constant_time (observe : nat -> nat) : Prop :=
  forall s1 s2 : nat, observe s1 = observe s2.`,
      template: `Theorem compose_ct : forall f g : nat -> nat,
  constant_time f ->
  constant_time g ->
  constant_time (fun x => g (f x)).
Proof.
  (* Use the CT property of f to rewrite the goal *)
Admitted.`,
      solution: `Theorem compose_ct : forall f g : nat -> nat,
  constant_time f ->
  constant_time g ->
  constant_time (fun x => g (f x)).
Proof.
  unfold constant_time.
  intros f g Hf Hg s1 s2.
  rewrite (Hf s1 s2).
  reflexivity.
Qed.`,
    },
    hint: 'After `unfold constant_time. intros f g Hf Hg s1 s2.`, the goal is `g (f s1) = g (f s2)`. Use `rewrite (Hf s1 s2).` to replace `f s1` with `f s2`, then `reflexivity`.',
    successMessage: 'Composition preserves constant-time! This modularity principle lets us verify security of individual components and compose them safely.',
  },

  /* ------------------------------------------------------------------
   * Step 5: Detecting Timing Leaks
   * ------------------------------------------------------------------ */
  {
    id: 5,
    title: 'Detecting Timing Leaks',
    explanation: `Even without observing branch directions, an attacker can measure **execution time**. If different branches take different amounts of time, the timing difference reveals which branch was taken.

Consider a program where the \`true\` branch takes 2 units and the \`false\` branch takes 5 units:
\`\`\`
Definition timing (secret : bool) : nat :=
  if secret then 2 else 5.
\`\`\`

Prove that this creates a timing leak: \`timing true <> timing false\`.

After \`unfold\` and \`simpl\`, the goal becomes \`2 <> 5\`, which \`discriminate\` solves since \`S (S O)\` and \`S (S (S (S (S O))))\` are structurally different.`,
    exercise: {
      prelude: `Definition timing (secret : bool) : nat :=
  if secret then 2 else 5.`,
      template: `Theorem timing_leak : timing true <> timing false.
Proof.
  (* Unfold and show the timing values differ *)
Admitted.`,
      solution: `Theorem timing_leak : timing true <> timing false.
Proof.
  unfold timing. simpl. discriminate.
Qed.`,
    },
    hint: 'Use `unfold timing. simpl.` to reduce the goal to `2 <> 5`, then `discriminate` proves the inequality.',
    successMessage: 'Timing difference detected! Real-world attacks like Lucky13 and Spectre exploit exactly these kinds of timing variations.',
  },

  /* ------------------------------------------------------------------
   * Step 6: Balanced Branches
   * ------------------------------------------------------------------ */
  {
    id: 6,
    title: 'Balanced Branches',
    explanation: `The defense against timing leaks: **balance the branches**. Both paths should take the same amount of time, so the attacker learns nothing from timing measurements.

\`\`\`
Definition balanced_timing (secret : bool) : nat :=
  if secret then 3 else 3.
\`\`\`

Both branches produce the same timing observation (\`3\`), making this constant-time.

\`\`\`
Definition no_timing_leak (f : bool -> nat) : Prop :=
  forall s1 s2 : bool, f s1 = f s2.
\`\`\`

Use \`destruct\` on both boolean arguments to enumerate all four cases, each of which is solved by \`reflexivity\`.`,
    exercise: {
      prelude: `Definition balanced_timing (secret : bool) : nat :=
  if secret then 3 else 3.

Definition no_timing_leak (f : bool -> nat) : Prop :=
  forall s1 s2 : bool, f s1 = f s2.`,
      template: `Theorem balanced_is_ct : no_timing_leak balanced_timing.
Proof.
  (* Enumerate all boolean cases *)
Admitted.`,
      solution: `Theorem balanced_is_ct : no_timing_leak balanced_timing.
Proof.
  unfold no_timing_leak, balanced_timing.
  intros s1 s2.
  destruct s1; destruct s2; reflexivity.
Qed.`,
    },
    hint: 'After `unfold no_timing_leak, balanced_timing. intros s1 s2.`, use `destruct s1; destruct s2; reflexivity.` to check all four boolean combinations.',
    successMessage: 'Balanced branches are constant-time! In practice, cryptographic libraries use techniques like constant-time comparison, conditional moves, and bitwise masking to eliminate all timing variations.',
  },
];
