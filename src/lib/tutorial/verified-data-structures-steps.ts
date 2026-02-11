import type { TutorialStep } from './types';

const bstPrelude = `Require Import Arith.
Require Import PeanoNat.

Inductive tree : Type :=
  | Leaf : tree
  | Node : nat -> tree -> tree -> tree.

Fixpoint lookup (x : nat) (t : tree) : bool :=
  match t with
  | Leaf => false
  | Node v l r =>
    match Nat.compare x v with
    | Lt => lookup x l
    | Eq => true
    | Gt => lookup x r
    end
  end.

Fixpoint insert (x : nat) (t : tree) : tree :=
  match t with
  | Leaf => Node x Leaf Leaf
  | Node v l r =>
    match Nat.compare x v with
    | Lt => Node v (insert x l) r
    | Eq => Node v l r
    | Gt => Node v l (insert x r)
    end
  end.

Inductive BST : nat -> nat -> tree -> Prop :=
  | BST_Leaf : forall lo hi, BST lo hi Leaf
  | BST_Node : forall lo hi v l r,
      lo <= v -> v <= hi ->
      BST lo v l -> BST v hi r ->
      BST lo hi (Node v l r).

Fixpoint size (t : tree) : nat :=
  match t with
  | Leaf => 0
  | Node _ l r => 1 + size l + size r
  end.`;

export const verifiedDataStructuresSteps: TutorialStep[] = [
  {
    id: 1,
    title: 'Binary Search Trees',
    explanation: `A **binary search tree** (BST) is a tree where each node's value is greater than all values in its left subtree and less than all in its right subtree.

We represent trees as an inductive type:
- \`Leaf\` — an empty tree
- \`Node v l r\` — a node with value \`v\`, left subtree \`l\`, right subtree \`r\`

The BST invariant is expressed as \`BST lo hi t\`: all values in \`t\` are between \`lo\` and \`hi\`. The constructors are:
- \`BST_Leaf\` — an empty tree satisfies the BST property for any bounds
- \`BST_Node\` — a node is a valid BST if \`lo <= v <= hi\` and both subtrees respect the bounds

**Your task:** Prove that \`Leaf\` is a valid BST with bounds 0 and 10. Apply the \`BST_Leaf\` constructor.`,
    exercise: {
      prelude: bstPrelude,
      template: `Theorem leaf_is_bst : BST 0 10 Leaf.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem leaf_is_bst : BST 0 10 Leaf.\nProof.\n  apply BST_Leaf.\nQed.`,
    },
    successMessage: 'A Leaf is trivially a BST for any bounds. BST_Leaf requires no premises — an empty tree has no values to violate the ordering. This is the base case for all BST proofs.',
    hint: 'apply BST_Leaf.',
  },
  {
    id: 2,
    title: 'Constructing BST Evidence',
    explanation: `To prove a concrete tree is a BST, you build evidence bottom-up using \`BST_Node\` and \`BST_Leaf\`.

For the tree \`Node 5 (Node 3 Leaf Leaf) (Node 7 Leaf Leaf)\`:
1. The left subtree \`Node 3 Leaf Leaf\` is a BST with bounds \`lo=0, hi=5\`
2. The right subtree \`Node 7 Leaf Leaf\` is a BST with bounds \`lo=5, hi=10\`
3. The root satisfies \`0 <= 5 <= 10\`

Each \`BST_Node\` application generates subgoals: the bound inequalities and BST evidence for subtrees.

**Your task:** Prove the tree \`Node 5 Leaf Leaf\` is a valid BST with bounds 0 and 10. Apply \`BST_Node\`, prove the inequalities with \`auto with arith\`, and apply \`BST_Leaf\` for the leaves.`,
    exercise: {
      prelude: bstPrelude,
      template: `Theorem simple_bst : BST 0 10 (Node 5 Leaf Leaf).\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem simple_bst : BST 0 10 (Node 5 Leaf Leaf).\nProof.\n  apply BST_Node.
  - auto with arith.
  - auto with arith.
  - apply BST_Leaf.
  - apply BST_Leaf.\nQed.`,
    },
    successMessage: 'You constructed BST evidence for a single-node tree! BST_Node required four premises: 0 <= 5, 5 <= 10, and BST proofs for both Leaf children. For larger trees, you\'d nest BST_Node applications.',
    hint: 'apply BST_Node. - auto with arith. - auto with arith. - apply BST_Leaf. - apply BST_Leaf.',
  },
  {
    id: 3,
    title: 'Lookup in a BST',
    explanation: `The \`lookup\` function searches a BST by comparing the target with each node's value and going left or right accordingly. It uses \`Nat.compare\` which returns \`Lt\`, \`Eq\`, or \`Gt\`.

A basic property: looking up any value in an empty tree returns \`false\`. This is immediate from the definition — \`lookup x Leaf = false\` for any \`x\`.

This simple fact is the base case for more complex lookup theorems. In the full VFA development, you'd prove that lookup respects the BST invariant: if a value was inserted, lookup finds it.

**Your task:** Prove that lookup in an empty tree always returns false.`,
    exercise: {
      prelude: bstPrelude,
      template: `Theorem lookup_leaf : forall x,\n  lookup x Leaf = false.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem lookup_leaf : forall x,\n  lookup x Leaf = false.\nProof.\n  intros x.\n  simpl.\n  reflexivity.\nQed.`,
    },
    successMessage: 'Lookup in a Leaf returns false by definition. This is the base case for proving lookup correctness. The interesting cases involve non-empty trees where Nat.compare guides the search.',
    hint: 'intros x. simpl. reflexivity.',
  },
  {
    id: 4,
    title: 'Insert Then Lookup',
    explanation: `The most important BST property: **if you insert a value, you can find it again**. Formally:

\`lookup x (insert x Leaf) = true\`

For a Leaf, \`insert x Leaf = Node x Leaf Leaf\`, and then \`lookup x (Node x Leaf Leaf)\` compares \`x\` with \`x\` using \`Nat.compare\`, which returns \`Eq\`, giving \`true\`.

The key lemma is \`Nat.compare_refl : forall n, Nat.compare n n = Eq\`, which tells us that comparing a number with itself always yields \`Eq\`.

**Your task:** Prove that inserting into a Leaf and looking up the same key returns true. After simplification, rewrite with \`Nat.compare_refl\`.`,
    exercise: {
      prelude: bstPrelude,
      template: `Theorem insert_lookup : forall x,\n  lookup x (insert x Leaf) = true.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem insert_lookup : forall x,\n  lookup x (insert x Leaf) = true.\nProof.\n  intros x.\n  simpl.\n  rewrite Nat.compare_refl.\n  reflexivity.\nQed.`,
    },
    successMessage: 'You proved the fundamental BST property for the base case! Nat.compare_refl told Coq that comparing x with itself yields Eq, making the lookup succeed. The general theorem (for any tree, not just Leaf) requires induction on the tree structure.',
    hint: 'intros x. simpl. rewrite Nat.compare_refl. reflexivity.',
  },
  {
    id: 5,
    title: 'Insert Preserves Other Keys',
    explanation: `Inserting a key should not affect the lookup of *other* keys. For a Leaf:

\`lookup y (insert x Leaf) = lookup y Leaf\` when \`x <> y\`

After inserting \`x\` into a Leaf, we get \`Node x Leaf Leaf\`. Looking up \`y\` (where \`y <> x\`) in this tree compares \`y\` with \`x\`, which returns either \`Lt\` or \`Gt\` (not \`Eq\`), leading to a lookup in a Leaf — which is \`false\`, matching \`lookup y Leaf\`.

We need to case-split on \`Nat.compare y x\` using \`destruct ... eqn:E\`. The \`Eq\` case is contradictory (since \`x <> y\`), which we resolve using \`Nat.compare_eq\`.

**Your task:** Prove that inserting \`x\` into a Leaf doesn't affect lookup of a different key \`y\`.`,
    exercise: {
      prelude: bstPrelude,
      template: `Theorem insert_leaf_other : forall x y,\n  x <> y ->\n  lookup y (insert x Leaf) = lookup y Leaf.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem insert_leaf_other : forall x y,\n  x <> y ->\n  lookup y (insert x Leaf) = lookup y Leaf.\nProof.\n  intros x y Hneq.\n  simpl.\n  destruct (Nat.compare y x) eqn:E.\n  - apply Nat.compare_eq in E. subst. contradiction.\n  - reflexivity.\n  - reflexivity.\nQed.`,
    },
    successMessage: 'You proved that insert doesn\'t affect other keys! The Eq case was impossible because Nat.compare_eq gives y = x, then subst rewrites the goal so contradiction can close it against x <> y. The Lt and Gt cases both led to lookup in Leaf. This is the "frame" property of BST insert.',
    hint: 'intros x y Hneq. simpl. destruct (Nat.compare y x) eqn:E. - apply Nat.compare_eq in E. subst. contradiction. - reflexivity. - reflexivity.',
  },
  {
    id: 6,
    title: 'Tree Size After Insert',
    explanation: `A structural property: inserting into a Leaf increases the tree size by exactly 1. The \`size\` function counts nodes recursively:
- \`size Leaf = 0\`
- \`size (Node v l r) = 1 + size l + size r\`

Since \`insert x Leaf = Node x Leaf Leaf\`, the size becomes \`1 + 0 + 0 = 1\`.

This is a simple computation, but it illustrates how we reason about structural properties of BST operations. The general theorem (size increases by at most 1 for any tree) would need induction on the tree with case analysis on \`Nat.compare\`.

**Your task:** Prove that the size of \`insert x Leaf\` is 1.`,
    exercise: {
      prelude: bstPrelude,
      template: `Theorem insert_leaf_size : forall x,\n  size (insert x Leaf) = 1.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem insert_leaf_size : forall x,\n  size (insert x Leaf) = 1.\nProof.\n  intros x.\n  simpl.\n  reflexivity.\nQed.`,
    },
    successMessage: 'Congratulations! You\'ve completed the Verified Data Structures tutorial. You\'ve defined BSTs with inductive invariants, proved lookup and insert properties, and established structural properties. These are the same techniques used in VFA (Verified Functional Algorithms) to build fully verified data structure libraries!',
    hint: 'intros x. simpl. reflexivity.',
  },
];
