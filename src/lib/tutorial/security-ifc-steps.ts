/**
 * @module security-ifc-steps
 *
 * Tutorial steps for "Security Type Systems" — the second tutorial in
 * the Security Foundations (SecF) volume group.
 *
 * Based on Software Foundations Volume 7, Chapter 3 (StaticIFC). This
 * tutorial introduces information-flow-control (IFC) type systems that
 * statically enforce noninterference. The key idea: security labels
 * propagate through expressions via a join (least upper bound) operation,
 * and assignments are only allowed when data flows downward or stays
 * at the same level.
 *
 * Concepts covered:
 *   1. Label join (least upper bound of security levels)
 *   2. Commutativity of join
 *   3. Join as an upper bound in the flow ordering
 *   4. Join as the *least* upper bound
 *   5. Taint tracking through expression evaluation
 *   6. The no-write-down principle (absurdity of High → Low flow)
 *
 * Tactics introduced/reinforced:
 *   - simpl, reflexivity, destruct, intros, exact, try, assumption,
 *     rewrite, unfold, simpl in, contradiction
 */
import type { TutorialStep } from './types';

export const securityIfcSteps: TutorialStep[] = [
  /* ------------------------------------------------------------------
   * Step 1: The Security Lattice
   * ------------------------------------------------------------------ */
  {
    id: 1,
    title: 'The Security Lattice',
    explanation: `IFC type systems track security labels through computations. When two values with different labels are combined (e.g., added together), the result must have a label that's **at least as high** as both inputs.

The \`join\` function computes this **least upper bound**:
\`\`\`
Definition join (l1 l2 : level) : level :=
  match l1, l2 with
  | Low, Low => Low
  | _, _ => High
  end.
\`\`\`

The only way to get a \`Low\` result is if **both** inputs are \`Low\`. Any \`High\` input "taints" the result.

Prove that joining two public values yields a public result.`,
    exercise: {
      prelude: `Inductive level : Type := | Low : level | High : level.

Definition join (l1 l2 : level) : level :=
  match l1, l2 with
  | Low, Low => Low
  | _, _ => High
  end.`,
      template: `Theorem join_low_low : join Low Low = Low.
Proof.
  (* Simplify the join computation *)
Admitted.`,
      solution: `Theorem join_low_low : join Low Low = Low.
Proof.
  simpl. reflexivity.
Qed.`,
    },
    hint: 'Use `simpl` to compute `join Low Low`, then `reflexivity` to close the goal.',
    successMessage: 'Two public values combined stay public — the base case of taint tracking!',
  },

  /* ------------------------------------------------------------------
   * Step 2: Join is Commutative
   * ------------------------------------------------------------------ */
  {
    id: 2,
    title: 'Join is Commutative',
    explanation: `For a security lattice to be well-behaved, the order in which we combine labels should not matter. That is, \`join l1 l2 = join l2 l1\`.

Since \`level\` has only two constructors, you can prove this by exhaustive case analysis on both arguments. There are 2×2 = 4 cases, and each reduces to a simple equality after \`simpl\`.

Use \`destruct l1; destruct l2\` to enumerate all four cases, then solve each with \`simpl; reflexivity\`.`,
    exercise: {
      prelude: `Inductive level : Type := | Low : level | High : level.

Definition join (l1 l2 : level) : level :=
  match l1, l2 with
  | Low, Low => Low
  | _, _ => High
  end.`,
      template: `Theorem join_comm : forall l1 l2 : level,
  join l1 l2 = join l2 l1.
Proof.
  (* Enumerate all four cases *)
Admitted.`,
      solution: `Theorem join_comm : forall l1 l2 : level,
  join l1 l2 = join l2 l1.
Proof.
  intros l1 l2.
  destruct l1; destruct l2; simpl; reflexivity.
Qed.`,
    },
    hint: 'After `intros l1 l2`, use `destruct l1; destruct l2; simpl; reflexivity.` — the semicolons chain tactics across all generated subgoals.',
    successMessage: 'Join is commutative — the order of operands does not affect the security label of the result.',
  },

  /* ------------------------------------------------------------------
   * Step 3: Join is an Upper Bound
   * ------------------------------------------------------------------ */
  {
    id: 3,
    title: 'Join is an Upper Bound',
    explanation: `The \`join\` of two labels must be **at least as high** as each input. This is what makes it an upper bound in the security lattice.

Formally: \`flows_to l1 (join l1 l2)\` — the first input can always flow to the join result.

The \`flows_to\` relation is:
\`\`\`
Definition flows_to (l1 l2 : level) : Prop :=
  match l1, l2 with
  | Low, _ => True
  | High, High => True
  | High, Low => False
  end.
\`\`\`

Enumerate all four combinations of \`l1\` and \`l2\`. After \`simpl\`, each case reduces to \`True\`.`,
    exercise: {
      prelude: `Inductive level : Type := | Low : level | High : level.

Definition join (l1 l2 : level) : level :=
  match l1, l2 with
  | Low, Low => Low
  | _, _ => High
  end.

Definition flows_to (l1 l2 : level) : Prop :=
  match l1, l2 with
  | Low, _ => True
  | High, High => True
  | High, Low => False
  end.`,
      template: `Theorem join_upper_left : forall l1 l2 : level,
  flows_to l1 (join l1 l2).
Proof.
  (* Case analysis on both levels *)
Admitted.`,
      solution: `Theorem join_upper_left : forall l1 l2 : level,
  flows_to l1 (join l1 l2).
Proof.
  intros l1 l2.
  destruct l1; destruct l2; simpl; exact I.
Qed.`,
    },
    hint: 'Use `intros l1 l2. destruct l1; destruct l2; simpl; exact I.` — all four cases reduce to `True`.',
    successMessage: 'Join is an upper bound — the result label is always at least as restrictive as each input.',
  },

  /* ------------------------------------------------------------------
   * Step 4: Join is the Least Upper Bound
   * ------------------------------------------------------------------ */
  {
    id: 4,
    title: 'Join is the Least Upper Bound',
    explanation: `\`join\` is not just any upper bound — it's the **least** upper bound. If some level \`l3\` is above both \`l1\` and \`l2\`, then it's also above \`join l1 l2\`.

\`\`\`
forall l1 l2 l3,
  flows_to l1 l3 ->
  flows_to l2 l3 ->
  flows_to (join l1 l2) l3
\`\`\`

This is a stronger property than being an upper bound. It requires 2×2×2 = 8 cases. After \`simpl in *\`:
- Most cases have goal \`True\` → solved by \`exact I\`
- Some cases have a hypothesis that is \`False\` → solved by \`assumption\`

The \`try\` combinator handles this: \`try exact I\` succeeds on \`True\` goals and is a no-op otherwise.`,
    exercise: {
      prelude: `Inductive level : Type := | Low : level | High : level.

Definition join (l1 l2 : level) : level :=
  match l1, l2 with
  | Low, Low => Low
  | _, _ => High
  end.

Definition flows_to (l1 l2 : level) : Prop :=
  match l1, l2 with
  | Low, _ => True
  | High, High => True
  | High, Low => False
  end.`,
      template: `Theorem join_least : forall l1 l2 l3 : level,
  flows_to l1 l3 ->
  flows_to l2 l3 ->
  flows_to (join l1 l2) l3.
Proof.
  (* Enumerate all 8 cases and handle each *)
Admitted.`,
      solution: `Theorem join_least : forall l1 l2 l3 : level,
  flows_to l1 l3 ->
  flows_to l2 l3 ->
  flows_to (join l1 l2) l3.
Proof.
  intros l1 l2 l3 H1 H2.
  destruct l1; destruct l2; destruct l3;
    simpl in *; try exact I; assumption.
Qed.`,
    },
    hint: 'After introducing all variables and hypotheses, use `destruct l1; destruct l2; destruct l3; simpl in *; try exact I; assumption.` to handle all 8 cases uniformly.',
    successMessage: 'Join is the least upper bound — this makes {Low, High} with `join` a proper lattice, the mathematical foundation of IFC type systems!',
  },

  /* ------------------------------------------------------------------
   * Step 5: Taint Tracking for Expressions
   * ------------------------------------------------------------------ */
  {
    id: 5,
    title: 'Taint Tracking for Expressions',
    explanation: `IFC type systems assign a security label to every expression. The label propagates through operations:

\`\`\`
Inductive expr : Type :=
  | EConst : nat -> expr   (* constants are Low *)
  | EVar : nat -> expr     (* variables get their label from env *)
  | EAdd : expr -> expr -> expr.  (* addition joins labels *)

Fixpoint label_of (e : expr) (env : nat -> level) : level :=
  match e with
  | EConst _ => Low
  | EVar x => env x
  | EAdd e1 e2 => join (label_of e1 env) (label_of e2 env)
  end.
\`\`\`

Prove that adding two expressions that are both \`Low\` produces a \`Low\` result. Use \`simpl\` to unfold \`label_of\`, then \`rewrite\` both hypotheses to substitute \`Low\`, then simplify \`join Low Low\`.`,
    exercise: {
      prelude: `Inductive level : Type := | Low : level | High : level.

Definition join (l1 l2 : level) : level :=
  match l1, l2 with
  | Low, Low => Low
  | _, _ => High
  end.

Inductive expr : Type :=
  | EConst : nat -> expr
  | EVar : nat -> expr
  | EAdd : expr -> expr -> expr.

Fixpoint label_of (e : expr) (env : nat -> level) : level :=
  match e with
  | EConst _ => Low
  | EVar x => env x
  | EAdd e1 e2 => join (label_of e1 env) (label_of e2 env)
  end.`,
      template: `Theorem add_public_public : forall e1 e2 env,
  label_of e1 env = Low ->
  label_of e2 env = Low ->
  label_of (EAdd e1 e2) env = Low.
Proof.
  (* Simplify label_of, rewrite hypotheses, simplify join *)
Admitted.`,
      solution: `Theorem add_public_public : forall e1 e2 env,
  label_of e1 env = Low ->
  label_of e2 env = Low ->
  label_of (EAdd e1 e2) env = Low.
Proof.
  intros e1 e2 env H1 H2.
  simpl.
  rewrite H1. rewrite H2.
  simpl. reflexivity.
Qed.`,
    },
    hint: 'After `intros`, use `simpl` to unfold `label_of` for `EAdd`. Then `rewrite H1. rewrite H2.` substitutes both sub-expression labels with `Low`. Finally `simpl. reflexivity.` computes `join Low Low = Low`.',
    successMessage: 'Taint tracking proved correct — two public sub-expressions produce a public result. This is how IFC type systems enforce noninterference at compile time!',
  },

  /* ------------------------------------------------------------------
   * Step 6: The No-Write-Down Principle
   * ------------------------------------------------------------------ */
  {
    id: 6,
    title: 'The No-Write-Down Principle',
    explanation: `The **no-write-down** rule (also called the *-property or "confinement") says: a process with access to \`High\` data must not write to \`Low\` channels. If it could, secret data would leak.

Formally, \`flows_to High Low\` is \`False\` — it's an impossible flow. If we assume such a flow exists, we can derive **anything** (ex falso quodlibet).

Prove that if High data could flow to Low, then any two natural numbers would be equal. This demonstrates the absurdity: allowing High → Low flow breaks the entire logic.

Use \`simpl in H\` to reduce the hypothesis to \`False\`, then \`contradiction\` to close the goal.`,
    exercise: {
      prelude: `Inductive level : Type := | Low : level | High : level.

Definition flows_to (l1 l2 : level) : Prop :=
  match l1, l2 with
  | Low, _ => True
  | High, High => True
  | High, Low => False
  end.`,
      template: `Theorem high_to_low_absurd : forall n m : nat,
  flows_to High Low -> n = m.
Proof.
  (* The hypothesis is absurd — derive anything *)
Admitted.`,
      solution: `Theorem high_to_low_absurd : forall n m : nat,
  flows_to High Low -> n = m.
Proof.
  intros n m H.
  simpl in H.
  contradiction.
Qed.`,
    },
    hint: 'After `intros n m H`, use `simpl in H` to reduce `flows_to High Low` to `False` in the hypothesis. Then `contradiction` closes the goal because we have `H : False`.',
    successMessage: 'The no-write-down principle: allowing High → Low flow leads to absurdity. This is why IFC type systems reject programs that write secrets to public channels!',
  },
];
