/**
 * Comprehensive Coq tactic documentation for LeetMethods.
 *
 * Each entry provides a short description, typical signature, example, and
 * cross-references so the UI can render rich hover / autocomplete info.
 */

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

export interface TacticDoc {
  name: string;
  category: string;
  signature: string;
  description: string;
  example: string;
  seeAlso: string[];
}

// ---------------------------------------------------------------------------
// Documentation entries
// ---------------------------------------------------------------------------

export const tacticDocs: TacticDoc[] = [
  // ===== Introduction =====
  {
    name: "intros",
    category: "Introduction",
    signature: "intros x y z",
    description:
      "Introduces one or more hypotheses or universally quantified variables from the goal into the proof context. If no names are given, Coq picks fresh names automatically.",
    example: `Goal forall (n m : nat), n + m = m + n.
Proof.
  intros n m.
  (* now n, m are in the context *)`,
    seeAlso: ["intro", "revert", "generalize"],
  },
  {
    name: "intro",
    category: "Introduction",
    signature: "intro x",
    description:
      "Introduces exactly one hypothesis or variable from the goal into the context. Fails if there is nothing to introduce.",
    example: `Goal forall n : nat, n = n.
Proof.
  intro n.
  reflexivity.
Qed.`,
    seeAlso: ["intros", "revert"],
  },

  // ===== Application =====
  {
    name: "apply",
    category: "Application",
    signature: "apply H",
    description:
      "Matches the conclusion of hypothesis or lemma H with the current goal and replaces it with the premises of H. Unification variables are created for any arguments that cannot be inferred.",
    example: `Goal forall P Q : Prop, (P -> Q) -> P -> Q.
Proof.
  intros P Q Hpq Hp.
  apply Hpq.
  exact Hp.
Qed.`,
    seeAlso: ["exact", "eapply", "apply .. in"],
  },
  {
    name: "exact",
    category: "Application",
    signature: "exact H",
    description:
      "Closes the current goal if term H has exactly the same type as the goal. Unlike apply, it does not generate subgoals.",
    example: `Goal forall P : Prop, P -> P.
Proof.
  intros P Hp.
  exact Hp.
Qed.`,
    seeAlso: ["apply", "assumption"],
  },
  {
    name: "assumption",
    category: "Application",
    signature: "assumption",
    description:
      "Searches the local context for a hypothesis whose type matches the goal exactly and closes it. Equivalent to trying exact on every hypothesis.",
    example: `Goal forall P : Prop, P -> P.
Proof.
  intros P Hp.
  assumption.
Qed.`,
    seeAlso: ["exact", "trivial", "auto"],
  },
  {
    name: "trivial",
    category: "Application",
    signature: "trivial",
    description:
      "Solves simple goals using a restricted subset of the auto proof-search strategy. It tries assumption, reflexivity, and the core hint databases but never introduces new hypotheses.",
    example: `Goal forall n : nat, n = n.
Proof.
  intro n. trivial.
Qed.`,
    seeAlso: ["auto", "assumption", "reflexivity"],
  },

  // ===== Automation =====
  {
    name: "auto",
    category: "Automation",
    signature: "auto",
    description:
      "Performs automatic proof search using the hint databases (core by default). It tries intros, apply, assumption, and registered hints up to a bounded depth.",
    example: `Goal forall P Q : Prop, P -> (P -> Q) -> Q.
Proof.
  auto.
Qed.`,
    seeAlso: ["eauto", "trivial", "intuition"],
  },
  {
    name: "eauto",
    category: "Automation",
    signature: "eauto",
    description:
      "Like auto, but uses eapply instead of apply, allowing existential variables. This makes it more powerful but potentially slower.",
    example: `Goal exists n : nat, n = 0.
Proof.
  eauto.
Qed.`,
    seeAlso: ["auto", "typeclasses eauto"],
  },

  // ===== Rewriting =====
  {
    name: "reflexivity",
    category: "Rewriting",
    signature: "reflexivity",
    description:
      "Closes a goal of the form x = x (or any reflexive relation). Also performs some definitional unfolding before checking.",
    example: `Goal 2 + 3 = 5.
Proof.
  reflexivity.
Qed.`,
    seeAlso: ["symmetry", "transitivity", "rewrite"],
  },
  {
    name: "symmetry",
    category: "Rewriting",
    signature: "symmetry",
    description:
      "Swaps the left- and right-hand sides of an equality (or symmetric relation) in the goal. Use 'symmetry in H' to apply it to a hypothesis.",
    example: `Goal forall n m : nat, n = m -> m = n.
Proof.
  intros n m H. symmetry. exact H.
Qed.`,
    seeAlso: ["reflexivity", "transitivity"],
  },
  {
    name: "transitivity",
    category: "Rewriting",
    signature: "transitivity y",
    description:
      "Splits an equality goal x = z into two subgoals x = y and y = z, where y is a term you supply.",
    example: `Goal forall a b c : nat, a = b -> b = c -> a = c.
Proof.
  intros a b c Hab Hbc.
  transitivity b.
  - exact Hab.
  - exact Hbc.
Qed.`,
    seeAlso: ["reflexivity", "symmetry", "rewrite"],
  },
  {
    name: "rewrite",
    category: "Rewriting",
    signature: "rewrite H | rewrite <- H | rewrite H in H2",
    description:
      "Replaces occurrences of the left-hand side of an equality H with the right-hand side in the goal. Use <- to rewrite right-to-left. Use 'in' to rewrite in a specific hypothesis.",
    example: `Goal forall n : nat, n = 0 -> n + n = 0.
Proof.
  intros n H.
  rewrite H.
  reflexivity.
Qed.`,
    seeAlso: ["replace", "subst", "symmetry"],
  },
  {
    name: "replace",
    category: "Rewriting",
    signature: "replace t1 with t2",
    description:
      "Replaces occurrences of t1 with t2 in the goal and generates a subgoal requiring you to prove t2 = t1. Useful when the rewriting direction is awkward.",
    example: `Goal forall n : nat, n + 0 = n.
Proof.
  intro n.
  replace (n + 0) with n.
  - reflexivity.
  - lia.
Qed.`,
    seeAlso: ["rewrite", "subst", "change"],
  },
  {
    name: "subst",
    category: "Rewriting",
    signature: "subst | subst x",
    description:
      "Finds hypotheses of the form x = e or e = x in the context, substitutes x everywhere, and removes the hypothesis. With an argument, it substitutes only the named variable.",
    example: `Goal forall n m : nat, n = m -> n + 1 = m + 1.
Proof.
  intros n m H. subst n.
  reflexivity.
Qed.`,
    seeAlso: ["rewrite", "replace"],
  },

  // ===== Simplification =====
  {
    name: "unfold",
    category: "Simplification",
    signature: "unfold f | unfold f in H",
    description:
      "Replaces a defined constant f with its definition in the goal or in a specified hypothesis. Useful when simpl does not reduce a user-defined function.",
    example: `Definition double n := n + n.
Goal double 3 = 6.
Proof.
  unfold double. reflexivity.
Qed.`,
    seeAlso: ["fold", "simpl", "cbv"],
  },
  {
    name: "fold",
    category: "Simplification",
    signature: "fold f",
    description:
      "The inverse of unfold: replaces the body of a definition with its name. Useful for readability after a partial simplification.",
    example: `Definition double n := n + n.
Goal 3 + 3 = double 3.
Proof.
  fold (double 3). reflexivity.
Qed.`,
    seeAlso: ["unfold", "change"],
  },
  {
    name: "simpl",
    category: "Simplification",
    signature: "simpl | simpl in H",
    description:
      "Performs beta-iota-zeta reduction and recursive function unfolding using a heuristic that avoids over-expanding. The most commonly used simplification tactic.",
    example: `Goal (fun x => x + 1) 3 = 4.
Proof.
  simpl. reflexivity.
Qed.`,
    seeAlso: ["unfold", "cbv", "lazy", "cbn"],
  },
  {
    name: "cbv",
    category: "Simplification",
    signature: "cbv | cbv beta delta iota",
    description:
      "Performs call-by-value full reduction. You can restrict which reduction steps are performed (beta, delta, iota, zeta, match, fix). More aggressive than simpl.",
    example: `Goal (fun x => x * 2) 5 = 10.
Proof.
  cbv. reflexivity.
Qed.`,
    seeAlso: ["simpl", "lazy", "vm_compute"],
  },
  {
    name: "lazy",
    category: "Simplification",
    signature: "lazy | lazy beta delta iota",
    description:
      "Performs call-by-need (lazy) reduction. Like cbv but only reduces sub-terms when needed. Can be more efficient than cbv on large terms.",
    example: `Goal (fun x => x) 42 = 42.
Proof.
  lazy. reflexivity.
Qed.`,
    seeAlso: ["cbv", "simpl"],
  },

  // ===== Case Analysis =====
  {
    name: "destruct",
    category: "Case Analysis",
    signature: "destruct x | destruct x as [| y z] | destruct x eqn:Heq",
    description:
      "Performs case analysis on x, generating one subgoal per constructor. The 'as' clause names the introduced variables; 'eqn:' records the case equation.",
    example: `Goal forall b : bool, b = true \\/ b = false.
Proof.
  intro b. destruct b.
  - left. reflexivity.
  - right. reflexivity.
Qed.`,
    seeAlso: ["induction", "case", "case_eq", "inversion"],
  },
  {
    name: "induction",
    category: "Case Analysis",
    signature: "induction n | induction n as [| n' IHn']",
    description:
      "Performs structural induction on n, generating a base case and one inductive case per recursive constructor, with an induction hypothesis for each recursive argument.",
    example: `Goal forall n : nat, 0 + n = n.
Proof.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.`,
    seeAlso: ["destruct", "elim", "fix"],
  },
  {
    name: "case",
    category: "Case Analysis",
    signature: "case x",
    description:
      "Performs case analysis similar to destruct, but does not substitute x in the goal. The original term remains and each branch gives the constructor form.",
    example: `Goal forall n : nat, n = 0 \\/ n <> 0.
Proof.
  intro n. case n.
  - left. reflexivity.
  - intros m. right. discriminate.
Qed.`,
    seeAlso: ["destruct", "case_eq"],
  },
  {
    name: "case_eq",
    category: "Case Analysis",
    signature: "case_eq x",
    description:
      "Like case, but additionally introduces an equation remembering the original value of x before the case split. Useful when you need to refer to the original value.",
    example: `Goal forall n : nat, (n =? 0) = true -> n = 0.
Proof.
  intros n H. case_eq n.
  - reflexivity.
  - intros m Hm. rewrite Hm in H. simpl in H. discriminate.
Qed.`,
    seeAlso: ["destruct", "case", "remember"],
  },
  {
    name: "elim",
    category: "Case Analysis",
    signature: "elim x",
    description:
      "Applies the elimination principle associated with the type of x. Lower-level than induction; useful when you need a custom elimination scheme.",
    example: `Goal forall n : nat, n = n.
Proof.
  intro n. elim n.
  - reflexivity.
  - intros m IH. reflexivity.
Qed.`,
    seeAlso: ["induction", "destruct"],
  },
  {
    name: "inversion",
    category: "Case Analysis",
    signature: "inversion H | inversion H as [...]",
    description:
      "Analyzes a hypothesis H by examining which constructors could have produced it, deriving equalities between arguments. Solves impossible cases automatically.",
    example: `Inductive even : nat -> Prop :=
  | even_O : even 0
  | even_SS : forall n, even n -> even (S (S n)).

Goal even 1 -> False.
Proof.
  intro H. inversion H.
Qed.`,
    seeAlso: ["destruct", "injection", "discriminate"],
  },
  {
    name: "injection",
    category: "Case Analysis",
    signature: "injection H | injection H as H1 H2",
    description:
      "Exploits injectivity of constructors: if C x1 = C x2 then x1 = x2. Introduces the derived equalities into the context.",
    example: `Goal forall n m : nat, S n = S m -> n = m.
Proof.
  intros n m H.
  injection H as H.
  exact H.
Qed.`,
    seeAlso: ["discriminate", "inversion"],
  },

  // ===== Logic =====
  {
    name: "split",
    category: "Logic",
    signature: "split",
    description:
      "Splits a conjunctive goal (A /\\ B) or biconditional (A <-> B) into two subgoals, one for each component.",
    example: `Goal True /\\ True.
Proof.
  split.
  - exact I.
  - exact I.
Qed.`,
    seeAlso: ["left", "right", "destruct", "constructor"],
  },
  {
    name: "left",
    category: "Logic",
    signature: "left",
    description:
      "Selects the left disjunct of a goal of the form A \\/ B, leaving A as the new goal.",
    example: `Goal True \\/ False.
Proof.
  left. exact I.
Qed.`,
    seeAlso: ["right", "split", "constructor"],
  },
  {
    name: "right",
    category: "Logic",
    signature: "right",
    description:
      "Selects the right disjunct of a goal of the form A \\/ B, leaving B as the new goal.",
    example: `Goal False \\/ True.
Proof.
  right. exact I.
Qed.`,
    seeAlso: ["left", "split", "constructor"],
  },
  {
    name: "exists",
    category: "Logic",
    signature: "exists t",
    description:
      "Provides a witness t for an existential goal (exists x, P x), replacing x with t in the remaining goal.",
    example: `Goal exists n : nat, n = 0.
Proof.
  exists 0. reflexivity.
Qed.`,
    seeAlso: ["constructor", "econstructor", "eauto"],
  },
  {
    name: "constructor",
    category: "Logic",
    signature: "constructor | constructor n",
    description:
      "Applies the first matching constructor of an inductive type to the goal. With an argument n, applies the n-th constructor specifically.",
    example: `Goal True.
Proof.
  constructor.
Qed.`,
    seeAlso: ["econstructor", "split", "left", "right", "exists"],
  },
  {
    name: "econstructor",
    category: "Logic",
    signature: "econstructor",
    description:
      "Like constructor, but allows existential variables for arguments that cannot be inferred immediately. Useful when some arguments will be determined later.",
    example: `Goal exists n : nat, n + 1 = 1.
Proof.
  econstructor. simpl. reflexivity.
Qed.`,
    seeAlso: ["constructor", "eexists", "eauto"],
  },

  // ===== Assertion =====
  {
    name: "assert",
    category: "Assertion",
    signature: "assert (H : P) | assert P as H by tac",
    description:
      "Introduces an intermediate lemma P as a new subgoal and adds hypothesis H : P to the context of the remaining goal. The 'by' clause can provide a tactic to prove P inline.",
    example: `Goal forall n : nat, n + 0 = n.
Proof.
  intro n.
  assert (H : 0 + n = n) by (simpl; reflexivity).
  lia.
Qed.`,
    seeAlso: ["pose", "cut", "enough", "set"],
  },
  {
    name: "pose",
    category: "Assertion",
    signature: "pose (x := t) | pose proof H as H2",
    description:
      "Introduces a local definition x := t into the context without generating a proof obligation. 'pose proof' copies and possibly specializes an existing term.",
    example: `Goal 3 + 2 = 5.
Proof.
  pose (x := 3 + 2).
  reflexivity.
Qed.`,
    seeAlso: ["set", "assert", "remember"],
  },
  {
    name: "set",
    category: "Assertion",
    signature: "set (x := t) | set (x := t) in *",
    description:
      "Like pose, but also replaces all occurrences of t in the goal (and optionally in hypotheses) with the new name x. Creates a transparent local definition.",
    example: `Goal (3 + 2) + (3 + 2) = 10.
Proof.
  set (x := 3 + 2).
  (* goal becomes x + x = 10 with x := 5 *)
  reflexivity.
Qed.`,
    seeAlso: ["pose", "remember", "assert"],
  },
  {
    name: "remember",
    category: "Assertion",
    signature: "remember t as x | remember t as x eqn:Heq",
    description:
      "Replaces t with a fresh variable x and adds an equation x = t to the context. Unlike set, the definition is opaque, preventing unwanted unfolding.",
    example: `Goal forall l : list nat, length (rev l) = length l.
Proof.
  intro l.
  remember (rev l) as l'.
  (* useful before induction to preserve equation *)`,
    seeAlso: ["set", "pose", "case_eq"],
  },
  {
    name: "cut",
    category: "Assertion",
    signature: "cut P",
    description:
      "Introduces an intermediate proposition P. Generates two subgoals: P -> <goal> and P. Essentially backward reasoning through an intermediate step.",
    example: `Goal forall n : nat, n = n.
Proof.
  intro n.
  cut (n + 0 = n).
  - intro H. reflexivity.
  - lia.
Qed.`,
    seeAlso: ["assert", "enough"],
  },
  {
    name: "enough",
    category: "Assertion",
    signature: "enough (H : P) | enough P as H by tac",
    description:
      "Like assert but reverses the subgoal order: first you prove the main goal assuming H, then you prove H. More natural for forward-reasoning proofs.",
    example: `Goal forall n : nat, n + 0 = n.
Proof.
  intro n.
  enough (H : n = n + 0) by lia.
  lia.
Qed.`,
    seeAlso: ["assert", "cut"],
  },
  {
    name: "specialize",
    category: "Assertion",
    signature: "specialize (H t1 t2) | specialize H with (x := t)",
    description:
      "Instantiates a universally quantified hypothesis H with specific arguments, replacing H with the specialized version in the context.",
    example: `Goal forall (f : nat -> nat), (forall x, f x = x) -> f 3 = 3.
Proof.
  intros f Hf.
  specialize (Hf 3).
  exact Hf.
Qed.`,
    seeAlso: ["apply", "generalize", "assert"],
  },

  // ===== Context Management =====
  {
    name: "generalize",
    category: "Context Management",
    signature: "generalize dependent x | generalize x",
    description:
      "The inverse of intro: moves a term or variable from the context back into the goal as a universally quantified variable. 'dependent' also reverts hypotheses that mention x.",
    example: `Goal forall n : nat, n = n.
Proof.
  intro n.
  generalize dependent n.
  intro n. reflexivity.
Qed.`,
    seeAlso: ["revert", "intros", "clear"],
  },
  {
    name: "dependent",
    category: "Context Management",
    signature: "dependent destruction x | dependent induction x",
    description:
      "Variants of destruction/induction that handle terms with dependencies. 'dependent destruction' uses the JMeq axiom to handle dependent pattern matching properly.",
    example: `Require Import Program.Equality.
Goal forall (n : nat) (v : Vector.t nat (S n)),
  Vector.hd v = Vector.hd v.
Proof.
  intros n v.
  dependent destruction v.
  simpl. reflexivity.
Qed.`,
    seeAlso: ["destruct", "induction", "inversion"],
  },
  {
    name: "clear",
    category: "Context Management",
    signature: "clear H | clear - H1 H2",
    description:
      "Removes a hypothesis from the context. 'clear - H1 H2' removes everything except H1 and H2. Useful for keeping the context tidy.",
    example: `Goal forall n m : nat, n = n.
Proof.
  intros n m.
  clear m.
  reflexivity.
Qed.`,
    seeAlso: ["clearbody", "revert", "rename"],
  },
  {
    name: "clearbody",
    category: "Context Management",
    signature: "clearbody x",
    description:
      "Removes the body of a local definition x from the context, keeping only the type. Turns a transparent let-binding into an opaque hypothesis.",
    example: `Goal let x := 5 in x = 5.
Proof.
  intro x.
  clearbody x.
  (* x is now opaque; goal is x = 5 *)`,
    seeAlso: ["clear", "set"],
  },
  {
    name: "rename",
    category: "Context Management",
    signature: "rename H into H'",
    description:
      "Renames a hypothesis in the proof context. Purely cosmetic; does not affect the proof term.",
    example: `Goal forall n : nat, n = n.
Proof.
  intro n.
  rename n into m.
  reflexivity.
Qed.`,
    seeAlso: ["clear", "move"],
  },
  {
    name: "move",
    category: "Context Management",
    signature: "move H after H' | move H before H' | move H at top | move H at bottom",
    description:
      "Reorders hypotheses in the proof context. This is a cosmetic operation that changes display order without affecting the proof.",
    example: `Goal forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  move m before n.
  lia.
Qed.`,
    seeAlso: ["rename", "clear", "revert"],
  },
  {
    name: "revert",
    category: "Context Management",
    signature: "revert x | revert dependent x",
    description:
      "Moves a hypothesis x from the context back into the goal as a universal quantification. The 'dependent' variant also reverts all hypotheses that depend on x.",
    example: `Goal forall n : nat, n = n.
Proof.
  intro n.
  revert n.
  intro n. reflexivity.
Qed.`,
    seeAlso: ["generalize", "intros", "clear"],
  },

  // ===== Automation / Contradiction =====
  {
    name: "exfalso",
    category: "Automation",
    signature: "exfalso",
    description:
      "Changes the current goal to False, allowing you to derive a contradiction from the hypotheses. Implements the ex falso quodlibet principle.",
    example: `Goal False -> 1 = 2.
Proof.
  intro H. exfalso. exact H.
Qed.`,
    seeAlso: ["contradiction", "discriminate", "absurd"],
  },
  {
    name: "contradiction",
    category: "Automation",
    signature: "contradiction",
    description:
      "Solves a goal when the context contains False or two contradictory hypotheses (H : P and H' : ~P). Combines exfalso with a search.",
    example: `Goal forall P : Prop, P -> ~P -> 1 = 2.
Proof.
  intros P Hp Hnp.
  contradiction.
Qed.`,
    seeAlso: ["exfalso", "discriminate", "congruence"],
  },
  {
    name: "discriminate",
    category: "Automation",
    signature: "discriminate | discriminate H",
    description:
      "Solves a goal when a hypothesis equates two structurally different constructors (e.g., S n = 0). Exploits the fact that distinct constructors are disjoint.",
    example: `Goal forall n : nat, S n = 0 -> False.
Proof.
  intros n H. discriminate H.
Qed.`,
    seeAlso: ["injection", "inversion", "contradiction"],
  },
  {
    name: "congruence",
    category: "Automation",
    signature: "congruence",
    description:
      "A decision procedure for equality with uninterpreted functions. Solves goals that follow from the congruence closure of hypotheses about equalities and disequalities.",
    example: `Goal forall (f : nat -> nat) (x y : nat),
  x = y -> f x = f y.
Proof.
  intros f x y H. congruence.
Qed.`,
    seeAlso: ["f_equal", "rewrite", "discriminate"],
  },

  // ===== Arithmetic =====
  {
    name: "omega",
    category: "Arithmetic",
    signature: "omega",
    description:
      "Solves linear arithmetic goals over nat and Z (Presburger arithmetic). Deprecated since Coq 8.12; use lia instead.",
    example: `Require Import Omega.
Goal forall n : nat, n + 1 > n.
Proof.
  intro n. omega.
Qed.`,
    seeAlso: ["lia", "nia", "ring"],
  },
  {
    name: "lia",
    category: "Arithmetic",
    signature: "lia",
    description:
      "Solves goals in linear integer arithmetic (Presburger arithmetic) over nat, Z, and N. The recommended replacement for omega.",
    example: `Require Import Lia.
Goal forall n m : nat, n <= m -> n + 1 <= m + 1.
Proof.
  intros n m H. lia.
Qed.`,
    seeAlso: ["nia", "omega", "ring"],
  },
  {
    name: "ring",
    category: "Arithmetic",
    signature: "ring",
    description:
      "Solves equalities in commutative (semi-)ring structures by normalizing both sides. Works on nat, Z, N, Q, and user-defined rings.",
    example: `Require Import Arith.
Goal forall n m : nat, (n + m) * (n + m) = n*n + 2*n*m + m*m.
Proof.
  intros n m. ring.
Qed.`,
    seeAlso: ["field", "lia", "nia"],
  },
  {
    name: "field",
    category: "Arithmetic",
    signature: "field",
    description:
      "Solves equalities in field structures (Q, R, etc.) by normalizing both sides. Generates side conditions for non-zero denominators.",
    example: `Require Import Reals. Open Scope R_scope.
Goal forall x : R, x <> 0 -> x / x = 1.
Proof.
  intros x Hx. field. exact Hx.
Qed.`,
    seeAlso: ["ring", "lra", "nia"],
  },
  {
    name: "fourier",
    category: "Arithmetic",
    signature: "fourier",
    description:
      "Solves linear arithmetic goals over real numbers using Fourier-Motzkin elimination. Deprecated; use lra instead.",
    example: `Require Import Reals Fourier. Open Scope R_scope.
Goal forall x : R, x > 0 -> x + 1 > 0.
Proof.
  intros x H. fourier.
Qed.`,
    seeAlso: ["lia", "field", "lra"],
  },
  {
    name: "nia",
    category: "Arithmetic",
    signature: "nia",
    description:
      "Non-linear integer arithmetic solver. Extends lia with limited support for multiplication and exponentiation. May not terminate on all inputs.",
    example: `Require Import Lia.
Goal forall n : nat, n * n >= 0.
Proof.
  intro n. nia.
Qed.`,
    seeAlso: ["lia", "psatz", "ring"],
  },
  {
    name: "psatz",
    category: "Arithmetic",
    signature: "psatz Z n | psatz R n",
    description:
      "Solves non-linear arithmetic goals using Positivstellensatz certificates. The argument n bounds the proof search depth. More powerful than nia but slower.",
    example: `Require Import Psatz.
Goal forall x : Z, (x * x >= 0)%Z.
Proof.
  intro x. psatz Z 2.
Qed.`,
    seeAlso: ["nia", "lia", "ring"],
  },

  // ===== Tacticals =====
  {
    name: "repeat",
    category: "Tacticals",
    signature: "repeat tac",
    description:
      "Applies tactic tac repeatedly until it fails. Always succeeds (even if tac fails immediately, yielding zero applications).",
    example: `Goal True /\\ True /\\ True /\\ True.
Proof.
  repeat split.
  all: exact I.
Qed.`,
    seeAlso: ["try", "do", "progress"],
  },
  {
    name: "try",
    category: "Tacticals",
    signature: "try tac",
    description:
      "Attempts to apply tac; if it fails, it does nothing and succeeds. Useful for making a tactic non-fatal.",
    example: `Goal 1 = 1.
Proof.
  try discriminate.  (* fails silently *)
  reflexivity.
Qed.`,
    seeAlso: ["repeat", "solve", "first"],
  },
  {
    name: "do",
    category: "Tacticals",
    signature: "do n tac",
    description:
      "Applies tactic tac exactly n times. Fails if tac fails before n applications have been performed.",
    example: `Goal True /\\ True /\\ True.
Proof.
  do 2 split.
  all: exact I.
Qed.`,
    seeAlso: ["repeat", "try"],
  },
  {
    name: "progress",
    category: "Tacticals",
    signature: "progress tac",
    description:
      "Applies tac and fails if the goal did not change. Useful inside repeat to ensure termination when tac would otherwise succeed vacuously.",
    example: `Goal 1 + 1 = 2.
Proof.
  progress simpl.  (* succeeds because the goal changed *)
  reflexivity.
Qed.`,
    seeAlso: ["repeat", "try", "fail"],
  },
  {
    name: "solve",
    category: "Tacticals",
    signature: "solve [tac1 | tac2 | ...]",
    description:
      "Tries each tactic in order and succeeds only if one of them completely solves the goal. Fails if no tactic solves it.",
    example: `Goal 1 = 1.
Proof.
  solve [reflexivity | auto].
Qed.`,
    seeAlso: ["first", "try", "now"],
  },
  {
    name: "now",
    category: "Tacticals",
    signature: "now tac",
    description:
      "Applies tac and then tries to close all remaining goals with easy (a combination of trivial tactics). Fails if any subgoal remains unsolved.",
    example: `Goal forall n : nat, n = n.
Proof.
  now intro n.
Qed.`,
    seeAlso: ["solve", "auto", "easy"],
  },
  {
    name: "first",
    category: "Tacticals",
    signature: "first [tac1 | tac2 | ...]",
    description:
      "Tries each tactic in order and uses the first one that succeeds, even if it does not fully solve the goal. Unlike solve, partial progress is accepted.",
    example: `Goal 1 = 1.
Proof.
  first [discriminate | reflexivity].
Qed.`,
    seeAlso: ["solve", "try"],
  },
  {
    name: "fail",
    category: "Tacticals",
    signature: "fail | fail n | fail \"message\"",
    description:
      "Always fails. Optionally takes a failure level n and a message. Useful inside try/repeat/match goal to abort a branch.",
    example: `Goal True.
Proof.
  (* try fail does nothing *)
  try fail.
  exact I.
Qed.`,
    seeAlso: ["idtac", "try", "solve"],
  },
  {
    name: "idtac",
    category: "Tacticals",
    signature: "idtac | idtac \"message\"",
    description:
      "The identity tactic: always succeeds and does nothing. Optionally prints a message. Useful as a no-op placeholder in tactical combinators.",
    example: `Goal True.
Proof.
  idtac "starting proof".
  exact I.
Qed.`,
    seeAlso: ["fail", "try"],
  },

  // ===== Computation =====
  {
    name: "f_equal",
    category: "Computation",
    signature: "f_equal",
    description:
      "Reduces a goal of the form f x1 = f x2 to proving x1 = x2 (and similarly for multiple arguments). Applies the congruence lemma for the head function.",
    example: `Goal forall n m : nat, n = m -> S n = S m.
Proof.
  intros n m H. f_equal. exact H.
Qed.`,
    seeAlso: ["congruence", "rewrite"],
  },
  {
    name: "change",
    category: "Computation",
    signature: "change t | change t1 with t2",
    description:
      "Replaces the goal with a convertible term t, or replaces occurrences of t1 with t2 when they are definitionally equal. Fails if the terms are not convertible.",
    example: `Goal (fun x => x) 5 = 5.
Proof.
  change ((fun x => x) 5) with 5.
  reflexivity.
Qed.`,
    seeAlso: ["replace", "unfold", "simpl"],
  },
  {
    name: "pattern",
    category: "Computation",
    signature: "pattern t | pattern t at n",
    description:
      "Performs beta-expansion, abstracting occurrences of term t in the goal into a function application. Useful to prepare the goal for apply or rewrite.",
    example: `Goal 0 + 0 = 0.
Proof.
  pattern 0 at 1.
  (* goal becomes (fun n => n + 0 = 0) 0 *)
  simpl. reflexivity.
Qed.`,
    seeAlso: ["change", "set", "unfold"],
  },
  {
    name: "vm_compute",
    category: "Computation",
    signature: "vm_compute",
    description:
      "Evaluates the goal using the optimized virtual machine. Much faster than cbv/simpl for heavy computation but produces opaque proof terms.",
    example: `Goal 2 ^ 10 = 1024.
Proof.
  vm_compute. reflexivity.
Qed.`,
    seeAlso: ["native_compute", "cbv", "simpl"],
  },
  {
    name: "native_compute",
    category: "Computation",
    signature: "native_compute",
    description:
      "Evaluates the goal by compiling to native OCaml code. The fastest reduction strategy in Coq, but requires native compilation support and produces opaque terms.",
    example: `Goal 2 ^ 20 = 1048576.
Proof.
  native_compute. reflexivity.
Qed.`,
    seeAlso: ["vm_compute", "cbv"],
  },

  // ===== Advanced =====
  {
    name: "admit",
    category: "Advanced",
    signature: "admit",
    description:
      "Closes the current goal without proof, leaving an axiom in the proof term. The resulting proof is incomplete and marked with Admitted instead of Qed.",
    example: `Goal forall P : Prop, P.
Proof.
  intro P.
  admit.
Admitted.`,
    seeAlso: ["give_up", "Admitted"],
  },
  {
    name: "give_up",
    category: "Advanced",
    signature: "give_up",
    description:
      "Abandons the current goal like admit, but is intended for use within proof scripts as a placeholder. The proof must still end with Admitted.",
    example: `Goal True /\\ False.
Proof.
  split.
  - exact I.
  - give_up.
Admitted.`,
    seeAlso: ["admit"],
  },
];

// ---------------------------------------------------------------------------
// Lookup map
// ---------------------------------------------------------------------------

export const tacticDocMap: Map<string, TacticDoc> = new Map(
  tacticDocs.map((doc) => [doc.name, doc])
);
