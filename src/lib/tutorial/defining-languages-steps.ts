import type { TutorialStep } from './types';

const aexpPrelude = `Require Import Arith.

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp).

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => aeval a1 + aeval a2
  | AMinus a1 a2 => aeval a1 - aeval a2
  end.`;

const optPrelude = `${aexpPrelude}

Fixpoint optimize_0plus (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) a2 => optimize_0plus a2
  | APlus a1 a2 => APlus (optimize_0plus a1) (optimize_0plus a2)
  | AMinus a1 a2 => AMinus (optimize_0plus a1) (optimize_0plus a2)
  end.`;

const bexpPrelude = `Require Import Arith.
Require Import PeanoNat.

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp).

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => aeval a1 + aeval a2
  | AMinus a1 a2 => aeval a1 - aeval a2
  end.

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => Nat.eqb (aeval a1) (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.`;

export const definingLanguagesSteps: TutorialStep[] = [
  {
    id: 1,
    title: 'Defining Expression Syntax',
    explanation: `Programming language theory starts with **defining languages formally**. We represent programs as inductive data types — their **abstract syntax trees** (ASTs).

Let's define a tiny arithmetic language with:
- \`ANum n\` — a literal number
- \`APlus a1 a2\` — addition of two expressions
- \`AMinus a1 a2\` — subtraction

We define an **evaluation function** \`aeval\` that recursively computes the value of an expression. For example, \`aeval (APlus (ANum 2) (ANum 3)) = 5\`.

This is exactly how real programming languages are formalized — first define the syntax as a data type, then define what it *means* as an evaluation function.

**Your task:** Prove that evaluating \`2 + 3\` gives \`5\`. After introducing, \`simpl\` will unfold the evaluation function, and \`reflexivity\` finishes it.`,
    exercise: {
      prelude: aexpPrelude,
      template: `Theorem aeval_example : aeval (APlus (ANum 2) (ANum 3)) = 5.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem aeval_example : aeval (APlus (ANum 2) (ANum 3)) = 5.\nProof.\n  simpl.\n  reflexivity.\nQed.`,
    },
    successMessage: 'Coq unfolded the evaluation function step by step: aeval (APlus (ANum 2) (ANum 3)) -> aeval (ANum 2) + aeval (ANum 3) -> 2 + 3 -> 5. This is how formal semantics works — you define evaluation and then reason about it.',
    hint: 'simpl. reflexivity.',
  },
  {
    id: 2,
    title: 'Optimizing Expressions',
    explanation: `A key application of formal languages is **verified optimization**. We define a transformation on expressions and prove it preserves meaning.

Our optimization: \`optimize_0plus\` removes additions with zero. Specifically, \`APlus (ANum 0) e\` is simplified to \`e\` (since \`0 + e = e\`). The optimizer recurses into subexpressions.

**Correctness** means: for any expression \`a\`, \`aeval (optimize_0plus a) = aeval a\`. The optimized expression evaluates to the same value as the original.

**Your task:** Prove correctness for a specific case: that optimizing \`0 + 5\` yields the same result as the original. This is a computation — \`simpl\` and \`reflexivity\` suffice.`,
    exercise: {
      prelude: optPrelude,
      template: `Theorem optimize_example :\n  aeval (optimize_0plus (APlus (ANum 0) (ANum 5))) = aeval (APlus (ANum 0) (ANum 5)).\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem optimize_example :\n  aeval (optimize_0plus (APlus (ANum 0) (ANum 5))) = aeval (APlus (ANum 0) (ANum 5)).\nProof.\n  simpl.\n  reflexivity.\nQed.`,
    },
    successMessage: 'The optimizer reduced APlus (ANum 0) (ANum 5) to ANum 5, and both evaluate to 5. Next we\'ll prove this holds for ALL expressions, not just this example.',
    hint: 'simpl. reflexivity.',
  },
  {
    id: 3,
    title: 'Proving Optimization Correct',
    explanation: `Now for the real challenge: prove the optimizer is correct for **all** expressions, not just a specific example.

\`forall a, aeval (optimize_0plus a) = aeval a\`

This requires **structural induction on \`a\`** (the expression). There are three cases:
- \`ANum n\`: trivial, the optimizer doesn't change numbers
- \`APlus a1 a2\`: we need to case-analyze whether \`a1\` is \`ANum 0\`
- \`AMinus a1 a2\`: recursive case, use both IHs

The \`APlus\` case is the interesting one. Use \`destruct a1\` to check if it's \`ANum n\`, then \`destruct n\` to check if it's 0.

**Your task:** Prove optimization correctness. The proof uses induction on \`a\`, with nested \`destruct\` for the APlus case.`,
    exercise: {
      prelude: optPrelude,
      template: `Theorem optimize_0plus_sound : forall a,\n  aeval (optimize_0plus a) = aeval a.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem optimize_0plus_sound : forall a,\n  aeval (optimize_0plus a) = aeval a.\nProof.\n  induction a.\n  - simpl. reflexivity.\n  - simpl. destruct a1.\n    + destruct n.\n      * simpl. apply IHa2.\n      * simpl. rewrite IHa2. reflexivity.\n    + simpl. rewrite IHa1. rewrite IHa2. reflexivity.\n    + simpl. rewrite IHa1. rewrite IHa2. reflexivity.\n  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.\nQed.`,
    },
    successMessage: 'You proved a real compiler optimization correct! The nested destruct handled the special case (APlus (ANum 0) _), and induction + rewrite handled all other cases. This is exactly how verified compilers like CompCert work — define an optimization, then prove it preserves semantics.',
    hint: 'induction a. For ANum: simpl; reflexivity. For APlus: simpl; destruct a1, then destruct n for ANum sub-case, using IHa1 and IHa2. For AMinus: simpl; rewrite IHa1; rewrite IHa2; reflexivity.',
  },
  {
    id: 4,
    title: 'Boolean Expressions and Evaluation',
    explanation: `Real languages have **boolean expressions** too. Let's extend our language:

- \`BTrue\` / \`BFalse\` — constants
- \`BEq a1 a2\` — equality test (are two arithmetic expressions equal?)
- \`BNot b\` — boolean negation
- \`BAnd b1 b2\` — boolean conjunction

The evaluator \`beval\` computes a \`bool\` by recursively evaluating subexpressions. For \`BEq\`, it evaluates both arithmetic sides and compares with \`Nat.eqb\`.

**Your task:** Prove that \`BNot BTrue\` evaluates to \`false\`. This is a direct computation.`,
    exercise: {
      prelude: bexpPrelude,
      template: `Theorem beval_not_true : beval (BNot BTrue) = false.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem beval_not_true : beval (BNot BTrue) = false.\nProof.\n  simpl.\n  reflexivity.\nQed.`,
    },
    successMessage: 'Boolean evaluation unfolds just like arithmetic evaluation. The BNot case applied negb to the result of evaluating BTrue. Now let\'s optimize boolean expressions too.',
    hint: 'simpl. reflexivity.',
  },
  {
    id: 5,
    title: 'Optimizing Short-Circuit And',
    explanation: `Just like we optimized \`0 + e\` to \`e\`, we can optimize **short-circuit evaluation**: \`BAnd BFalse b2\` can be simplified to \`BFalse\` since \`false && anything = false\`.

Our optimizer \`optimize_bfalse\` removes short-circuit \`BAnd BFalse _\` patterns and recurses into subexpressions.

**Your task:** Prove this optimization is correct: for any boolean expression, the optimized version evaluates to the same boolean. This requires induction on \`b\`. The key case is \`BAnd\`, where you need to case-split on \`b1\` to handle the \`BFalse\` pattern.`,
    exercise: {
      prelude: `Require Import Arith.
Require Import PeanoNat.
Require Import Bool.

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp).

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => aeval a1 + aeval a2
  | AMinus a1 a2 => aeval a1 - aeval a2
  end.

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => Nat.eqb (aeval a1) (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_bfalse (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq a1 a2
  | BNot b1 => BNot (optimize_bfalse b1)
  | BAnd BFalse _ => BFalse
  | BAnd b1 b2 => BAnd (optimize_bfalse b1) (optimize_bfalse b2)
  end.`,
      template: `Theorem optimize_bfalse_sound : forall b,\n  beval (optimize_bfalse b) = beval b.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem optimize_bfalse_sound : forall b,\n  beval (optimize_bfalse b) = beval b.\nProof.\n  induction b.\n  - simpl. reflexivity.\n  - simpl. reflexivity.\n  - simpl. reflexivity.\n  - simpl. rewrite IHb. reflexivity.\n  - simpl. destruct b1.\n    + simpl. rewrite IHb2. reflexivity.\n    + simpl. reflexivity.\n    + simpl. rewrite IHb2. reflexivity.\n    + simpl. rewrite IHb1. rewrite IHb2. reflexivity.\n    + simpl. rewrite IHb1. rewrite IHb2. reflexivity.\nQed.`,
    },
    successMessage: 'You verified a short-circuit optimization! The BAnd case required destructing b1 to handle the BFalse pattern separately. The pattern is always the same: define an optimization, prove it preserves evaluation. This is the heart of verified compilation.',
    hint: 'induction b. First three cases: simpl; reflexivity. For BNot: simpl; rewrite IHb; reflexivity. For BAnd: simpl; destruct b1 to handle the BFalse short-circuit case separately, using IHb1 and IHb2 in the other cases.',
  },
  {
    id: 6,
    title: 'Cross-Language Properties',
    explanation: `Let's prove a property that connects arithmetic and boolean expressions: if two arithmetic expressions evaluate to the same value, then \`BEq\` of those expressions evaluates to \`true\`.

This requires:
- Understanding how \`beval\` handles \`BEq\` (it uses \`Nat.eqb\`)
- The standard library fact \`Nat.eqb_refl : forall n, Nat.eqb n n = true\`

**Your task:** Prove that \`BEq a a\` always evaluates to \`true\`. After simplifying, you need to show \`Nat.eqb (aeval a) (aeval a) = true\`, which follows from \`Nat.eqb_refl\`.`,
    exercise: {
      prelude: bexpPrelude,
      template: `Theorem beq_refl : forall a,\n  beval (BEq a a) = true.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem beq_refl : forall a,\n  beval (BEq a a) = true.\nProof.\n  intros a.\n  simpl.\n  apply Nat.eqb_refl.\nQed.`,
    },
    successMessage: 'Congratulations! You\'ve completed the Defining Languages tutorial. You\'ve defined arithmetic and boolean expression languages, written evaluation functions, proved optimizations correct, and connected the two languages. These are the same techniques used in real verified compilers like CompCert and CertiCoq!',
    hint: 'intros a. simpl. apply Nat.eqb_refl.',
  },
];
