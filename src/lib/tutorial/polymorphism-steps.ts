import type { TutorialStep } from './types';

export const polymorphismSteps: TutorialStep[] = [
  {
    id: 1,
    title: 'Polymorphic Types and Functions',
    explanation: `**Polymorphism** lets you write functions and theorems that work for *any* type, not just a specific one like \`nat\` or \`bool\`.

In Coq, a polymorphic function like the identity function has type \`forall A : Type, A -> A\`. The \`forall A : Type\` means "for any type A." When you apply this function, Coq infers or you specify which type \`A\` is.

You've already seen polymorphism in list theorems like \`forall (A : Type) (l : list A), l ++ [] = l\`. The \`A : Type\` parameter makes it work for lists of *anything*.

**Your task:** Prove that the polymorphic identity function applied to any value returns that value. This is straightforward — introduce the type and value, then use \`reflexivity\`.`,
    exercise: {
      prelude: '(* No imports needed *)',
      template: `Theorem poly_id_correct : forall (A : Type) (x : A),\n  (fun (T : Type) (v : T) => v) A x = x.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem poly_id_correct : forall (A : Type) (x : A),\n  (fun (T : Type) (v : T) => v) A x = x.\nProof.\n  intros A x.\n  simpl.\n  reflexivity.\nQed.`,
    },
    successMessage: 'You proved your first polymorphic theorem! The key insight is that "forall A : Type" works just like "forall n : nat" — you introduce it with intros and work with it abstractly.',
    hint: 'intros A x. simpl. reflexivity.',
  },
  {
    id: 2,
    title: 'Polymorphic Pairs and Projections',
    explanation: `Coq's standard library provides polymorphic pairs: \`(a, b)\` has type \`A * B\`. The projection functions \`fst\` and \`snd\` extract the components:
- \`fst (a, b) = a\`
- \`snd (a, b) = b\`

To work with a pair hypothesis, you can \`destruct\` it: if \`p : A * B\`, then \`destruct p as [a b]\` gives you \`a : A\` and \`b : B\`.

**Your task:** Prove that \`fst\` applied to a constructed pair returns the first component. This is a direct computation — after introducing all variables, \`simpl\` and \`reflexivity\` handle it.`,
    exercise: {
      prelude: '(* No imports needed *)',
      template: `Theorem fst_pair : forall (A B : Type) (a : A) (b : B),\n  fst (a, b) = a.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem fst_pair : forall (A B : Type) (a : A) (b : B),\n  fst (a, b) = a.\nProof.\n  intros A B a b.\n  simpl.\n  reflexivity.\nQed.`,
    },
    successMessage: 'Polymorphic pairs work exactly like you\'d expect. The fst projection just computes to the first element. Next we\'ll see how polymorphism interacts with lists.',
    hint: 'intros A B a b. simpl. reflexivity.',
  },
  {
    id: 3,
    title: 'The map Function',
    explanation: `**Higher-order functions** take other functions as arguments. The most important one is **\`map\`**: given a function \`f : A -> B\` and a list \`l : list A\`, \`map f l\` applies \`f\` to every element, producing a \`list B\`.

For example: \`map S [1; 2; 3] = [2; 3; 4]\`.

An important property: \`map\` preserves the length of the list. Proving this requires **induction on the list**, since \`map\` is defined recursively.

The pattern is familiar from Tutorial 2: base case is trivial, inductive step uses \`simpl\` to unfold \`map\` and \`length\`, then \`rewrite\` with the IH.

**Your task:** Prove that \`length (map f l) = length l\` for any function \`f\` and list \`l\`.`,
    exercise: {
      prelude: 'Require Import List.\nImport ListNotations.',
      template: `Theorem map_length : forall (A B : Type) (f : A -> B) (l : list A),\n  length (map f l) = length l.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem map_length : forall (A B : Type) (f : A -> B) (l : list A),\n  length (map f l) = length l.\nProof.\n  intros A B f l.\n  induction l as [| x l' IHl'].\n  - simpl. reflexivity.\n  - simpl. rewrite IHl'. reflexivity.\nQed.`,
    },
    successMessage: 'You proved that map preserves length using the standard induction pattern. Notice how the proof structure mirrors the recursive definition of map: base case for nil, inductive step for cons.',
    hint: 'induction l as [| x l\' IHl\']. - simpl. reflexivity. - simpl. rewrite IHl\'. reflexivity.',
  },
  {
    id: 4,
    title: 'Map Distributes Over Composition',
    explanation: `A key property of \`map\` is that it **distributes over function composition**: applying \`map (fun x => g (f x))\` is the same as first mapping \`f\`, then mapping \`g\`.

In symbols: \`map g (map f l) = map (fun x => g (f x)) l\`.

This is the "functor law" — it says map respects composition. The proof follows the same induction pattern as the previous step.

**Your task:** Prove map distributes over composition. Induct on the list, simplify, and use the induction hypothesis.`,
    exercise: {
      prelude: 'Require Import List.\nImport ListNotations.',
      template: `Theorem map_map : forall (A B C : Type) (f : A -> B) (g : B -> C) (l : list A),\n  map g (map f l) = map (fun x => g (f x)) l.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem map_map : forall (A B C : Type) (f : A -> B) (g : B -> C) (l : list A),\n  map g (map f l) = map (fun x => g (f x)) l.\nProof.\n  intros A B C f g l.\n  induction l as [| x l' IHl'].\n  - simpl. reflexivity.\n  - simpl. rewrite IHl'. reflexivity.\nQed.`,
    },
    successMessage: 'You proved the functor law for map! This property is fundamental in functional programming. Notice how the induction proof has become second nature — the pattern is always the same for properties of recursive list functions.',
    hint: 'induction l as [| x l\' IHl\']. - simpl. reflexivity. - simpl. rewrite IHl\'. reflexivity.',
  },
  {
    id: 5,
    title: 'Fold: Reducing Lists',
    explanation: `**\`fold_right\`** is the most powerful higher-order list function. It "folds" a list using a combining function and a base value:

\`fold_right f base [x1; x2; x3] = f x1 (f x2 (f x3 base))\`

For example:
- \`fold_right plus 0 [1; 2; 3] = 1 + (2 + (3 + 0)) = 6\` (sum)
- \`fold_right app [] [l1; l2; l3] = l1 ++ (l2 ++ (l3 ++ []))\` (flatten)

Many list functions can be defined in terms of fold_right. For instance, \`map f l = fold_right (fun x acc => f x :: acc) [] l\`.

**Your task:** Prove that folding \`cons\` over a list with \`[]\` as the base returns the original list. This shows that fold_right with the list constructors is the identity.`,
    exercise: {
      prelude: 'Require Import List.\nImport ListNotations.',
      template: `Theorem fold_right_cons_nil : forall (A : Type) (l : list A),\n  fold_right cons nil l = l.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem fold_right_cons_nil : forall (A : Type) (l : list A),\n  fold_right cons nil l = l.\nProof.\n  intros A l.\n  induction l as [| x l' IHl'].\n  - simpl. reflexivity.\n  - simpl. rewrite IHl'. reflexivity.\nQed.`,
    },
    successMessage: 'This result is sometimes called the "universal property" of fold_right: folding with the constructors (cons/nil) is the identity. It shows that fold_right can reconstruct any list transformation.',
    hint: 'induction l as [| x l\' IHl\']. - simpl. reflexivity. - simpl. rewrite IHl\'. reflexivity.',
  },
  {
    id: 6,
    title: 'Filter Distributes Over Append',
    explanation: `The **\`filter\`** function keeps only elements satisfying a boolean predicate: \`filter f [1;2;3;4]\` with \`f = even\` gives \`[2;4]\`.

An important property is that filter **distributes over append**: filtering a concatenated list is the same as concatenating the filtered halves.

\`filter f (l1 ++ l2) = filter f l1 ++ filter f l2\`

The proof requires induction on \`l1\`. In the inductive step, you'll need \`destruct (f x)\` to case-split on whether the head element passes the filter.

**Your task:** Prove filter distributes over append. This combines induction, destruct on booleans, simpl, and rewrite.`,
    exercise: {
      prelude: 'Require Import List.\nImport ListNotations.\nRequire Import Bool.',
      template: `Theorem filter_app : forall (A : Type) (f : A -> bool) (l1 l2 : list A),\n  filter f (l1 ++ l2) = filter f l1 ++ filter f l2.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem filter_app : forall (A : Type) (f : A -> bool) (l1 l2 : list A),\n  filter f (l1 ++ l2) = filter f l1 ++ filter f l2.\nProof.\n  intros A f l1 l2.\n  induction l1 as [| x l1' IHl1'].\n  - simpl. reflexivity.\n  - simpl. rewrite IHl1'. destruct (f x).\n    + simpl. reflexivity.\n    + reflexivity.\nQed.`,
    },
    successMessage: 'Congratulations! You\'ve completed the Polymorphism & Higher-Order Functions tutorial. You now understand polymorphic types, map, fold_right, and filter — the building blocks of functional programming. These higher-order patterns will appear throughout the remaining tutorials.',
    hint: 'induction l1 as [| x l1\' IHl1\']. - simpl. reflexivity. - simpl. rewrite IHl1\'. destruct (f x). + simpl. reflexivity. + reflexivity.',
  },
];
