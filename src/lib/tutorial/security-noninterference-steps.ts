/**
 * @module security-noninterference-steps
 *
 * Tutorial steps for "Noninterference & Secrecy" — the first tutorial in
 * the Security Foundations (SecF) volume group.
 *
 * Based on Software Foundations Volume 7 (Security Foundations) by
 * Cătălin Hriţcu and Yonghyun Kim. This tutorial introduces the
 * foundational concept of noninterference: a program is secure if
 * changing secret inputs does not affect publicly observable outputs.
 *
 * Concepts covered:
 *   1. Security levels (Low/High classification)
 *   2. Information flow ordering (which flows are allowed)
 *   3. Reflexivity of the flow relation
 *   4. Transitivity of the flow relation
 *   5. Noninterference for pure functions
 *   6. Detecting information leaks (proving insecurity)
 *
 * Tactics introduced/reinforced:
 *   - discriminate, simpl, exact, destruct, unfold, intros,
 *     reflexivity, exists, try, assumption
 */
import type { TutorialStep } from './types';

export const securityNoninterferenceSteps: TutorialStep[] = [
  /* ------------------------------------------------------------------
   * Step 1: Security Levels
   * ------------------------------------------------------------------ */
  {
    id: 1,
    title: 'Security Levels',
    explanation: `In security, we classify data by its **sensitivity level**. The simplest model uses two levels:

- \`Low\` — public data that anyone can see
- \`High\` — secret data that must be protected

This two-point lattice is the foundation of **information flow control** (IFC), a key topic in Software Foundations Volume 7.

The prelude defines:
\`\`\`
Inductive level : Type :=
  | Low : level
  | High : level.
\`\`\`

Your first task: prove that \`Low\` and \`High\` are distinct. The \`discriminate\` tactic solves goals of the form \`X <> Y\` when X and Y are different constructors.`,
    exercise: {
      prelude: 'Inductive level : Type := | Low : level | High : level.',
      template: `Theorem low_not_high : Low <> High.
Proof.
  (* Use discriminate to distinguish constructors *)
Admitted.`,
      solution: `Theorem low_not_high : Low <> High.
Proof.
  discriminate.
Qed.`,
    },
    hint: 'The `discriminate` tactic automatically proves that two different constructors are not equal. Just type: discriminate.',
    successMessage: 'Low and High are provably distinct — the foundation of any security policy!',
  },

  /* ------------------------------------------------------------------
   * Step 2: Information Flow Ordering
   * ------------------------------------------------------------------ */
  {
    id: 2,
    title: 'Information Flow Ordering',
    explanation: `Not all data flows are allowed in a secure system. The fundamental rule:

- **Low → High is allowed**: Public data can be treated as secret (it's safe to be overly cautious)
- **High → Low is forbidden**: Secret data must never leak to public channels

We model this with a \`flows_to\` relation:
\`\`\`
Definition flows_to (l1 l2 : level) : Prop :=
  match l1, l2 with
  | Low, _ => True
  | High, High => True
  | High, Low => False
  end.
\`\`\`

Prove that Low data is allowed to flow to High. After \`simpl\`, the goal reduces to \`True\`, which you can close with \`exact I\` (where \`I\` is the constructor of \`True\`).`,
    exercise: {
      prelude: `Inductive level : Type := | Low : level | High : level.

Definition flows_to (l1 l2 : level) : Prop :=
  match l1, l2 with
  | Low, _ => True
  | High, High => True
  | High, Low => False
  end.`,
      template: `Theorem low_flows_to_high : flows_to Low High.
Proof.
  (* Simplify and prove True *)
Admitted.`,
      solution: `Theorem low_flows_to_high : flows_to Low High.
Proof.
  simpl. exact I.
Qed.`,
    },
    hint: 'Use `simpl` to reduce `flows_to Low High` to `True`, then `exact I` to prove `True`.',
    successMessage: 'Public data can safely flow to secret contexts — this is the "no read up" principle!',
  },

  /* ------------------------------------------------------------------
   * Step 3: Flow is Reflexive
   * ------------------------------------------------------------------ */
  {
    id: 3,
    title: 'Flow is Reflexive',
    explanation: `Data should always be allowed to stay at its own security level. This means \`flows_to\` must be **reflexive**: for any level \`l\`, \`flows_to l l\` holds.

Since \`level\` has only two constructors (\`Low\` and \`High\`), you can prove this by case analysis using \`destruct\`. Each case will simplify to \`True\`.

Try:
1. \`intros l\` to name the universally quantified variable
2. \`destruct l\` to split into the \`Low\` and \`High\` cases
3. \`simpl\` and \`exact I\` in each case (or combine with \`;\`)`,
    exercise: {
      prelude: `Inductive level : Type := | Low : level | High : level.

Definition flows_to (l1 l2 : level) : Prop :=
  match l1, l2 with
  | Low, _ => True
  | High, High => True
  | High, Low => False
  end.`,
      template: `Theorem flows_to_refl : forall l : level, flows_to l l.
Proof.
  (* Case analysis on l *)
Admitted.`,
      solution: `Theorem flows_to_refl : forall l : level, flows_to l l.
Proof.
  intros l. destruct l; simpl; exact I.
Qed.`,
    },
    hint: 'Use `intros l. destruct l; simpl; exact I.` — the semicolon applies `simpl; exact I` to both cases generated by `destruct`.',
    successMessage: 'The flow relation is reflexive — data can always remain at its own level.',
  },

  /* ------------------------------------------------------------------
   * Step 4: Flow is Transitive
   * ------------------------------------------------------------------ */
  {
    id: 4,
    title: 'Flow is Transitive',
    explanation: `If data can flow from level A to B, and from B to C, then it can flow from A to C. This **transitivity** property ensures the security policy is coherent.

This proof requires case analysis on **three** variables (\`l1\`, \`l2\`, \`l3\`), giving 2×2×2 = 8 cases. After \`simpl in *\`, each case either:
- Has goal \`True\` → solved by \`exact I\`
- Has a hypothesis \`H : False\` → solved by \`assumption\`

The \`try\` combinator lets you attempt a tactic that might fail: \`try exact I\` will succeed on \`True\` goals and silently do nothing on others.`,
    exercise: {
      prelude: `Inductive level : Type := | Low : level | High : level.

Definition flows_to (l1 l2 : level) : Prop :=
  match l1, l2 with
  | Low, _ => True
  | High, High => True
  | High, Low => False
  end.`,
      template: `Theorem flows_to_trans : forall l1 l2 l3 : level,
  flows_to l1 l2 -> flows_to l2 l3 -> flows_to l1 l3.
Proof.
  (* Introduce everything, then enumerate all 8 cases *)
Admitted.`,
      solution: `Theorem flows_to_trans : forall l1 l2 l3 : level,
  flows_to l1 l2 -> flows_to l2 l3 -> flows_to l1 l3.
Proof.
  intros l1 l2 l3 H1 H2.
  destruct l1; destruct l2; destruct l3;
    simpl in *; try exact I; assumption.
Qed.`,
    },
    hint: 'After `intros l1 l2 l3 H1 H2`, use `destruct l1; destruct l2; destruct l3` to enumerate all 8 cases. Then `simpl in *; try exact I; assumption.` handles them all.',
    successMessage: 'Transitivity proved! Together with reflexivity, this makes `flows_to` a preorder — exactly what a security lattice needs.',
  },

  /* ------------------------------------------------------------------
   * Step 5: Noninterfering Functions
   * ------------------------------------------------------------------ */
  {
    id: 5,
    title: 'Noninterfering Functions',
    explanation: `The core security property: a function is **noninterfering** if changing the secret (private) input does not change the output.

Formally, for a function \`f(pub, priv)\`:
\`\`\`
Definition noninterfering (f : nat -> nat -> nat) : Prop :=
  forall (pub priv1 priv2 : nat),
    f pub priv1 = f pub priv2.
\`\`\`

The function \`fun pub priv => pub\` (projection on the public input) is clearly secure — it ignores the secret entirely.

Use \`unfold noninterfering\` to expand the definition, then \`intros\` and \`reflexivity\`.`,
    exercise: {
      prelude: `Definition noninterfering (f : nat -> nat -> nat) : Prop :=
  forall (pub priv1 priv2 : nat), f pub priv1 = f pub priv2.`,
      template: `Theorem projection_secure :
  noninterfering (fun pub priv => pub).
Proof.
  (* Unfold the definition and prove equality *)
Admitted.`,
      solution: `Theorem projection_secure :
  noninterfering (fun pub priv => pub).
Proof.
  unfold noninterfering.
  intros pub priv1 priv2.
  reflexivity.
Qed.`,
    },
    hint: 'Use `unfold noninterfering` to expand the definition. Then `intros pub priv1 priv2` gives you the variables. The goal `pub = pub` is solved by `reflexivity`.',
    successMessage: 'A function that ignores secrets is trivially secure — this is the simplest form of noninterference!',
  },

  /* ------------------------------------------------------------------
   * Step 6: Detecting Information Leaks
   * ------------------------------------------------------------------ */
  {
    id: 6,
    title: 'Detecting Information Leaks',
    explanation: `Security isn't just about proving programs secure — we must also **detect insecure programs**. A function leaks secrets if there exist inputs where changing the secret changes the output:

\`\`\`
Definition leaks_secret (f : nat -> nat -> nat) : Prop :=
  exists pub priv1 priv2 : nat,
    f pub priv1 <> f pub priv2.
\`\`\`

Consider \`fun pub priv => pub + priv\` — adding the secret to the output clearly leaks it. To prove this:
1. \`unfold leaks_secret\` to expand the definition
2. Provide witnesses with \`exists\`: pub=0, priv1=0, priv2=1
3. \`simpl\` to compute: \`0 + 0 = 0\` and \`0 + 1 = 1\`
4. \`discriminate\` to prove \`0 <> 1\``,
    exercise: {
      prelude: `Definition leaks_secret (f : nat -> nat -> nat) : Prop :=
  exists pub priv1 priv2 : nat, f pub priv1 <> f pub priv2.`,
      template: `Theorem add_leaks :
  leaks_secret (fun pub priv => pub + priv).
Proof.
  (* Provide concrete witness values that demonstrate the leak *)
Admitted.`,
      solution: `Theorem add_leaks :
  leaks_secret (fun pub priv => pub + priv).
Proof.
  unfold leaks_secret.
  exists 0. exists 0. exists 1.
  simpl. discriminate.
Qed.`,
    },
    hint: 'After `unfold leaks_secret`, use `exists 0. exists 0. exists 1.` to provide witness values. Then `simpl` computes 0+0=0 and 0+1=1, and `discriminate` proves 0 <> 1.',
    successMessage: 'You proved a function is insecure by finding a concrete counterexample — this is the essence of security testing meets formal verification!',
  },
];
