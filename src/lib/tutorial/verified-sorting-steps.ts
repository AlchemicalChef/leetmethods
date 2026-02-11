import type { TutorialStep } from './types';

const sortedPrelude = `Require Import List.
Import ListNotations.

Inductive sorted : list nat -> Prop :=
  | sorted_nil : sorted []
  | sorted_one : forall x, sorted [x]
  | sorted_cons : forall x y l,
      x <= y -> sorted (y :: l) -> sorted (x :: y :: l).`;

const insertPrelude = `Require Import List.
Import ListNotations.
Require Import Arith.
Require Import PeanoNat.

Fixpoint insert (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => [x]
  | h :: t => if x <=? h then x :: h :: t else h :: insert x t
  end.`;

const fullPrelude = `Require Import List.
Import ListNotations.
Require Import Arith.
Require Import PeanoNat.

Inductive sorted : list nat -> Prop :=
  | sorted_nil : sorted []
  | sorted_one : forall x, sorted [x]
  | sorted_cons : forall x y l,
      x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Fixpoint insert (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => [x]
  | h :: t => if x <=? h then x :: h :: t else h :: insert x t
  end.`;

export const verifiedSortingSteps: TutorialStep[] = [
  {
    id: 1,
    title: 'What Does "Sorted" Mean?',
    explanation: `To verify a sorting algorithm, we first need to define what "sorted" means formally. We use an **inductive proposition**:

A list is sorted if:
- The empty list is sorted (\`sorted_nil\`)
- A singleton list is sorted (\`sorted_one\`)
- For \`a :: b :: l\`, the list is sorted if \`a <= b\` and \`b :: l\` is sorted (\`sorted_cons\`)

This is a recursive property: each adjacent pair must be in order.

**Your task:** Prove that the list \`[1; 3; 5]\` is sorted by constructing evidence using the constructors. Apply \`sorted_cons\`, provide the \`<=\` evidence using \`auto with arith\`, and recurse.`,
    exercise: {
      prelude: sortedPrelude,
      template: `Theorem sorted_1_3_5 : sorted [1; 3; 5].\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem sorted_1_3_5 : sorted [1; 3; 5].\nProof.\n  apply sorted_cons.\n  - auto with arith.\n  - apply sorted_cons.\n    + auto with arith.\n    + apply sorted_one.\nQed.`,
    },
    successMessage: 'You built evidence of sortedness by proving each adjacent pair is in order. The "auto with arith" tactic handled the inequality proofs (1 <= 3 and 3 <= 5). This inductive definition is the standard way to specify sortedness.',
    hint: 'apply sorted_cons. - auto with arith. - apply sorted_cons. + auto with arith. + apply sorted_one.',
  },
  {
    id: 2,
    title: 'The Insert Function',
    explanation: `The core of **insertion sort** is the \`insert\` function: given a number and a sorted list, insert the number at the right position to keep the list sorted.

\`insert x l\` walks through \`l\`, comparing \`x\` with each element:
- If \`x <= head\`, put \`x\` before the head
- Otherwise, keep the head and recurse on the tail

A basic property: the length of the result is one more than the original. This doesn't require sortedness — it's purely structural.

**Your task:** Prove that \`insert\` increases the length by 1. Use induction on \`l\`, with \`destruct\` on the comparison in the cons case.`,
    exercise: {
      prelude: insertPrelude,
      template: `Theorem insert_length : forall x l,\n  length (insert x l) = S (length l).\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem insert_length : forall x l,\n  length (insert x l) = S (length l).\nProof.\n  intros x l.\n  induction l as [| h t IHt].\n  - simpl. reflexivity.\n  - simpl. destruct (x <=? h).\n    + simpl. reflexivity.\n    + simpl. rewrite IHt. reflexivity.\nQed.`,
    },
    successMessage: 'You proved a structural property of insert. The destruct on (x <=? h) handled both cases: when x goes before h (length increases immediately) and when x goes after h (induction hypothesis applies). This pattern of destructing boolean comparisons will recur throughout this tutorial.',
    hint: 'induction l as [| h t IHt]. - simpl. reflexivity. - simpl. destruct (x <=? h). + simpl. reflexivity. + simpl. rewrite IHt. reflexivity.',
  },
  {
    id: 3,
    title: 'Sortedness Preservation — Base Cases',
    explanation: `Before proving the full preservation theorem, let's warm up with a simpler property: inserting into an empty list always produces a sorted list.

This is straightforward: \`insert x [] = [x]\`, and singleton lists are sorted by \`sorted_one\`.

We also need to understand how \`<=?\` (the boolean less-than-or-equal, \`Nat.leb\`) relates to \`<=\` (the propositional version). The key bridge lemma is \`Nat.leb_le : forall n m, (n <=? m) = true <-> n <= m\`.

**Your task:** Prove that inserting into an empty list gives a sorted result. After simplification, apply \`sorted_one\`.`,
    exercise: {
      prelude: fullPrelude,
      template: `Theorem insert_nil_sorted : forall x,\n  sorted (insert x []).\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem insert_nil_sorted : forall x,\n  sorted (insert x []).\nProof.\n  intros x.\n  simpl.\n  apply sorted_one.\nQed.`,
    },
    successMessage: 'Simple but important! insert x [] = [x], and [x] is sorted. This is the base case for the full preservation proof. Now let\'s build insertion sort.',
    hint: 'intros x. simpl. apply sorted_one.',
  },
  {
    id: 4,
    title: 'Building Insertion Sort',
    explanation: `**Insertion sort** is simply: fold \`insert\` over the input list, starting from the empty list.

\`insertion_sort [3; 1; 2]\`
= \`insert 3 (insert 1 (insert 2 []))\`
= \`insert 3 (insert 1 [2])\`
= \`insert 3 [1; 2]\`
= \`[1; 2; 3]\`

An important property: insertion sort preserves length. The proof uses induction on the input list and the \`insert_length\` lemma from Step 2.

**Your task:** Prove that insertion sort preserves length. Induct on \`l\` and use the \`insert_length\` lemma (provided in the prelude).`,
    exercise: {
      prelude: `${insertPrelude}

Fixpoint insertion_sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert h (insertion_sort t)
  end.

Lemma insert_length : forall x l,
  length (insert x l) = S (length l).
Proof.
  intros x l. induction l as [| h t IHt].
  - simpl. reflexivity.
  - simpl. destruct (x <=? h); simpl; try rewrite IHt; reflexivity.
Qed.`,
      template: `Theorem sort_length : forall l,\n  length (insertion_sort l) = length l.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem sort_length : forall l,\n  length (insertion_sort l) = length l.\nProof.\n  induction l as [| h t IHt].\n  - simpl. reflexivity.\n  - simpl. rewrite insert_length. rewrite IHt. reflexivity.\nQed.`,
    },
    successMessage: 'You proved length preservation by combining induction with the insert_length lemma. The inductive step showed: length (insert h (insertion_sort t)) = S (length (insertion_sort t)) = S (length t) = length (h :: t). Composing lemmas like this is how real verification proofs are structured.',
    hint: 'induction l as [| h t IHt]. - simpl. reflexivity. - simpl. rewrite insert_length. rewrite IHt. reflexivity.',
  },
  {
    id: 5,
    title: 'Sorting a Concrete List',
    explanation: `Before tackling the general sortedness proof (which is quite involved), let's verify that insertion sort correctly sorts a specific list.

For concrete inputs, Coq can *compute* the result of \`insertion_sort\` and we can then prove sortedness of the result directly.

**Your task:** Prove that \`insertion_sort [3; 1; 2]\` is sorted. After \`simpl\`, Coq computes the result to \`[1; 2; 3]\`, and you construct sortedness evidence.`,
    exercise: {
      prelude: `${fullPrelude}

Fixpoint insertion_sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert h (insertion_sort t)
  end.`,
      template: `Theorem sort_3_1_2_sorted : sorted (insertion_sort [3; 1; 2]).\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem sort_3_1_2_sorted : sorted (insertion_sort [3; 1; 2]).\nProof.\n  simpl.\n  apply sorted_cons.\n  - auto with arith.\n  - apply sorted_cons.\n    + auto with arith.\n    + apply sorted_one.\nQed.`,
    },
    successMessage: 'Coq computed insertion_sort [3; 1; 2] = [1; 2; 3], and you proved [1; 2; 3] is sorted. For concrete lists, computation + manual evidence construction works. The general proof (for all lists) would require proving that insert preserves sortedness.',
    hint: 'simpl. apply sorted_cons. - auto with arith. - apply sorted_cons. + auto with arith. + apply sorted_one.',
  },
  {
    id: 6,
    title: 'Insert Preserves Sortedness (Singleton)',
    explanation: `The central lemma for insertion sort correctness is: **if \`l\` is sorted, then \`insert x l\` is sorted.**

The full proof requires induction on the sortedness evidence. Let's prove the singleton case: inserting into a one-element sorted list produces a sorted result.

The proof case-splits on \`x <=? y\` using \`destruct ... eqn:E\`:
- If \`x <=? y = true\`: \`insert x [y] = [x; y]\`, and we need \`x <= y\` from \`Nat.leb_le\`
- If \`x <=? y = false\`: \`insert x [y] = [y; x]\`, and we need \`y <= x\` from the negation

**Your task:** Prove the singleton case. Use \`destruct (x <=? y) eqn:E\` and the \`Nat.leb_le\` bridge lemma.`,
    exercise: {
      prelude: `${fullPrelude}
Require Import Bool.`,
      template: `Theorem insert_sorted_singleton : forall x y,\n  sorted (insert x [y]).\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem insert_sorted_singleton : forall x y,\n  sorted (insert x [y]).\nProof.\n  intros x y.\n  simpl.\n  destruct (x <=? y) eqn:E.\n  - apply sorted_cons.\n    + apply Nat.leb_le. exact E.\n    + apply sorted_one.\n  - apply sorted_cons.\n    + apply Nat.leb_gt in E. auto with arith.\n    + apply sorted_one.\nQed.`,
    },
    successMessage: 'Congratulations! You\'ve completed the Verified Sorting tutorial. You defined sortedness inductively, implemented insertion sort, proved length preservation, verified concrete examples, and proved the key insert-preserves-sortedness lemma. These are the same techniques used in VFA (Verified Functional Algorithms) to build fully verified sorting implementations!',
    hint: 'intros x y. simpl. destruct (x <=? y) eqn:E. Both cases: apply sorted_cons, prove the inequality using Nat.leb_le or Nat.leb_gt, then apply sorted_one.',
  },
];
