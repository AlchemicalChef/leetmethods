import type { TutorialStep } from './types';

const typingPrelude = `Inductive ty : Type :=
  | TNat
  | TBool.

Inductive expr : Type :=
  | ENum (n : nat)
  | EBool (b : bool)
  | EPlus (e1 e2 : expr)
  | EAnd (e1 e2 : expr).

Inductive has_type : expr -> ty -> Prop :=
  | T_Num : forall n, has_type (ENum n) TNat
  | T_Bool : forall b, has_type (EBool b) TBool
  | T_Plus : forall e1 e2,
      has_type e1 TNat -> has_type e2 TNat ->
      has_type (EPlus e1 e2) TNat
  | T_And : forall e1 e2,
      has_type e1 TBool -> has_type e2 TBool ->
      has_type (EAnd e1 e2) TBool.`;

const evalPrelude = `${typingPrelude}

Inductive val : Type :=
  | VNat (n : nat)
  | VBool (b : bool).

Fixpoint eval_expr (e : expr) : option val :=
  match e with
  | ENum n => Some (VNat n)
  | EBool b => Some (VBool b)
  | EPlus e1 e2 =>
    match eval_expr e1, eval_expr e2 with
    | Some (VNat n1), Some (VNat n2) => Some (VNat (n1 + n2))
    | _, _ => None
    end
  | EAnd e1 e2 =>
    match eval_expr e1, eval_expr e2 with
    | Some (VBool b1), Some (VBool b2) => Some (VBool (andb b1 b2))
    | _, _ => None
    end
  end.`;

export const typeSystemsSteps: TutorialStep[] = [
  {
    id: 1,
    title: 'Types for Expressions',
    explanation: `A **type system** assigns types to expressions and rejects ill-typed programs *before* execution. This is **static analysis** — catching errors at compile time.

We'll define a simple expression language with two types:
- \`TNat\` — natural number type
- \`TBool\` — boolean type

Expressions include constants (\`ENum\`, \`EBool\`), \`EPlus\` (arithmetic), and \`EAnd\` (boolean). The typing relation \`has_type e t\` says "expression \`e\` has type \`t\`."

The key insight: \`EPlus\` requires both arguments to be \`TNat\`, and \`EAnd\` requires both to be \`TBool\`. This prevents nonsensical expressions like adding a number to a boolean.

**Your task:** Prove that \`ENum 3\` has type \`TNat\` by applying the appropriate typing rule.`,
    exercise: {
      prelude: typingPrelude,
      template: `Theorem num_has_type : has_type (ENum 3) TNat.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem num_has_type : has_type (ENum 3) TNat.\nProof.\n  apply T_Num.\nQed.`,
    },
    successMessage: 'You applied the T_Num typing rule, which says any ENum n has type TNat. Typing rules are just inductive proposition constructors — proving something is well-typed means constructing evidence using these rules.',
    hint: 'apply T_Num.',
  },
  {
    id: 2,
    title: 'Typing Derivations',
    explanation: `For compound expressions, you build a **typing derivation** by composing rules bottom-up:

To type \`EPlus (ENum 2) (ENum 3)\`:
1. \`T_Num\` gives \`has_type (ENum 2) TNat\`
2. \`T_Num\` gives \`has_type (ENum 3) TNat\`
3. \`T_Plus\` combines them: \`has_type (EPlus (ENum 2) (ENum 3)) TNat\`

This is like building a proof tree. The \`apply\` tactic does the work: \`apply T_Plus\` generates subgoals for each premise.

**Your task:** Prove that \`EPlus (ENum 2) (ENum 3)\` has type \`TNat\`. Apply \`T_Plus\`, then apply \`T_Num\` for each subgoal.`,
    exercise: {
      prelude: typingPrelude,
      template: `Theorem plus_has_type :\n  has_type (EPlus (ENum 2) (ENum 3)) TNat.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem plus_has_type :\n  has_type (EPlus (ENum 2) (ENum 3)) TNat.\nProof.\n  apply T_Plus.\n  - apply T_Num.\n  - apply T_Num.\nQed.`,
    },
    successMessage: 'You built a typing derivation! T_Plus required two premises (both TNat), and T_Num provided each one. This tree structure is exactly how type checkers work internally.',
    hint: 'apply T_Plus. - apply T_Num. - apply T_Num.',
  },
  {
    id: 3,
    title: 'Types Are Unique',
    explanation: `A crucial property of our type system is **type uniqueness**: every expression has at most one type. If \`has_type e t1\` and \`has_type e t2\`, then \`t1 = t2\`.

This property guarantees the type system is **deterministic** — there's no ambiguity.

The proof strategy: induction on the first typing derivation \`H1\`, then \`inversion\` on the second \`H2\` to see which rule was used. Since each expression form has exactly one typing rule, the types must match.

**Your task:** Prove type uniqueness. Use \`induction H1\`, then \`inversion H2\` in each case, and conclude with \`reflexivity\`.`,
    exercise: {
      prelude: typingPrelude,
      template: `Theorem type_uniqueness : forall e t1 t2,\n  has_type e t1 -> has_type e t2 -> t1 = t2.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem type_uniqueness : forall e t1 t2,\n  has_type e t1 -> has_type e t2 -> t1 = t2.\nProof.\n  intros e t1 t2 H1 H2.\n  induction H1; inversion H2; reflexivity.\nQed.`,
    },
    successMessage: 'A beautiful one-line proof! For each typing rule in H1, inversion on H2 showed only the same rule could apply, so the types must be equal. This is type uniqueness — a hallmark of well-designed type systems.',
    hint: 'intros e t1 t2 H1 H2. induction H1; inversion H2; reflexivity.',
  },
  {
    id: 4,
    title: 'Evaluation and Values',
    explanation: `Now let's add evaluation. Our expressions evaluate to **values** — either natural numbers or booleans. We use an inductive type \`val\` to represent runtime values.

The evaluator \`eval_expr\` returns \`option val\` because ill-typed expressions (like \`EPlus (EBool true) (ENum 1)\`) cannot be evaluated meaningfully — they return \`None\`.

A key insight: **well-typed expressions always evaluate successfully** (they never return \`None\`). This is the **progress** property — a well-typed term can always make progress.

**Your task:** Prove that evaluating a number literal returns the corresponding value. This is a simple computation.`,
    exercise: {
      prelude: evalPrelude,
      template: `Theorem eval_num : forall n,\n  eval_expr (ENum n) = Some (VNat n).\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem eval_num : forall n,\n  eval_expr (ENum n) = Some (VNat n).\nProof.\n  intros n.\n  simpl.\n  reflexivity.\nQed.`,
    },
    successMessage: 'Number literals always evaluate to their corresponding value. This is the base case for proving that well-typed expressions always succeed. Next we\'ll see what happens with ill-typed expressions.',
    hint: 'intros n. simpl. reflexivity.',
  },
  {
    id: 5,
    title: 'Ill-Typed Expressions Can Fail',
    explanation: `What happens when you try to evaluate an ill-typed expression like \`EPlus (EBool true) (ENum 1)\` — adding a boolean to a number?

The evaluator returns \`None\` because the \`EPlus\` case expects both sub-results to be \`VNat\`, but \`EBool true\` evaluates to \`VBool true\`.

This demonstrates why type systems exist: they **reject programs before execution** that would fail at runtime. The **type safety theorem** says: if an expression is well-typed, evaluation *never* returns \`None\`.

**Your task:** Prove that the ill-typed expression \`EPlus (EBool true) (ENum 1)\` evaluates to \`None\`.`,
    exercise: {
      prelude: evalPrelude,
      template: `Theorem ill_typed_fails :\n  eval_expr (EPlus (EBool true) (ENum 1)) = None.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem ill_typed_fails :\n  eval_expr (EPlus (EBool true) (ENum 1)) = None.\nProof.\n  simpl.\n  reflexivity.\nQed.`,
    },
    successMessage: 'The evaluator returned None because it expected two VNat values for EPlus, but got VBool. Type systems prevent exactly this kind of runtime error. Now let\'s prove the type safety theorem!',
    hint: 'simpl. reflexivity.',
  },
  {
    id: 6,
    title: 'Well-Typed Expressions Evaluate Successfully',
    explanation: `**Type safety** is the crown jewel of type theory. It says: "well-typed programs don't go wrong."

We'll prove a key building block: if both subexpressions of \`EPlus\` evaluate to natural number values, then the whole expression evaluates successfully.

The proof uses \`rewrite\` to substitute the known evaluation results into the \`eval_expr\` computation, making the match arms reduce.

The full type safety theorem (for all well-typed expressions) would use induction on the typing derivation. This step shows the essential technique.

**Your task:** Prove that if both sides of a plus evaluate to nats, the whole expression evaluates to their sum.`,
    exercise: {
      prelude: evalPrelude,
      template: `Theorem plus_progress : forall e1 e2 n1 n2,\n  eval_expr e1 = Some (VNat n1) ->\n  eval_expr e2 = Some (VNat n2) ->\n  eval_expr (EPlus e1 e2) = Some (VNat (n1 + n2)).\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem plus_progress : forall e1 e2 n1 n2,\n  eval_expr e1 = Some (VNat n1) ->\n  eval_expr e2 = Some (VNat n2) ->\n  eval_expr (EPlus e1 e2) = Some (VNat (n1 + n2)).\nProof.\n  intros e1 e2 n1 n2 H1 H2.\n  simpl.\n  rewrite H1.\n  rewrite H2.\n  reflexivity.\nQed.`,
    },
    successMessage: 'Congratulations! You\'ve completed the Type Systems tutorial. You\'ve defined typing rules as inductive propositions, built typing derivations, proved type uniqueness, and established type safety. These are the same techniques used to verify real programming languages like ML, Haskell, and Rust\'s type checker!',
    hint: 'intros e1 e2 n1 n2 H1 H2. simpl. rewrite H1. rewrite H2. reflexivity.',
  },
];
