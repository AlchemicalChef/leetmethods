import type { TutorialStep } from './tutorial-steps';

export const appliedMethodsSteps: TutorialStep[] = [
  {
    id: 1,
    title: 'Destructing Hypotheses',
    explanation: `In the basics tutorial you learned \`intros\`, \`exact\`, \`apply\`, and \`split\`. Now we'll go deeper.

**\`destruct\`** is used to break apart compound hypotheses. If you have \`H : A /\\ B\` (a conjunction), \`destruct H as [HA HB]\` gives you two separate hypotheses \`HA : A\` and \`HB : B\`.

For disjunctions \`H : A \\/ B\`, \`destruct H as [HA | HB]\` creates **two subgoals**: one where you assume \`A\`, another where you assume \`B\`. You prove each case separately.

**Note the syntax difference:** conjunctions use \`[HA HB]\` (space-separated, both available at once), disjunctions use \`[HA | HB]\` (pipe-separated, one per subgoal).

**Your task:** Prove that conjunction implies disjunction: if \`P /\\ Q\`, then \`P \\/ Q\`. You need to destruct the conjunction, then choose which side of the disjunction to prove.`,
    exercise: {
      prelude: '(* No imports needed *)',
      template: `Theorem and_implies_or : forall P Q : Prop,\n  P /\\ Q -> P \\/ Q.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem and_implies_or : forall P Q : Prop,\n  P /\\ Q -> P \\/ Q.\nProof.\n  intros P Q H.\n  destruct H as [HP HQ].\n  left.\n  exact HP.\nQed.`,
    },
    successMessage: 'You destructed a conjunction and used "left" to pick which side of the disjunction to prove. You could also have used "right" with HQ.',
    hint: 'intros P Q H. destruct H as [HP HQ]. left. exact HP.',
  },
  {
    id: 2,
    title: 'Case Analysis on Data',
    explanation: `\`destruct\` isn't just for logical connectives — it works on any inductive type. The most common use is **case analysis** on booleans and natural numbers.

For a boolean \`b\`: \`destruct b\` creates two subgoals — one where \`b = true\` and one where \`b = false\`.

For a natural number \`n\`: \`destruct n\` creates two subgoals — one for \`n = 0\` and one for \`n = S n'\` (where \`n'\` is the predecessor).

**The \`eqn:\` modifier** is very useful: \`destruct b eqn:E\` does the case split AND adds a hypothesis \`E\` recording which case you're in (e.g., \`E : b = true\`).

**Your task:** Prove that \`negb (negb b) = b\` for any boolean. You need to case-split on \`b\` and simplify each case.`,
    exercise: {
      prelude: 'Require Import Bool.',
      template: `Theorem negb_involutive : forall b : bool,\n  negb (negb b) = b.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem negb_involutive : forall b : bool,\n  negb (negb b) = b.\nProof.\n  intros b.\n  destruct b.\n  - simpl. reflexivity.\n  - simpl. reflexivity.\nQed.`,
    },
    successMessage: 'Case analysis on booleans is one of the simplest but most useful techniques. Each case reduces to a concrete computation that Coq can verify.',
    hint: 'intros b. destruct b. - simpl. reflexivity. - simpl. reflexivity.',
  },
  {
    id: 3,
    title: 'Simplification and Computation',
    explanation: `Coq can compute with definitions. The key tactics for computation are:

**\`simpl\`** — Unfolds function definitions and reduces the goal. For example, if the goal is \`2 + 3 = 5\`, \`simpl\` reduces it to \`5 = 5\`.

**\`reflexivity\`** — Proves \`x = x\` (any expression equal to itself). It also does computation internally, so \`reflexivity\` alone can sometimes prove things like \`2 + 3 = 5\` without needing \`simpl\` first.

**\`unfold\`** — Explicitly unfolds a specific definition. Useful when \`simpl\` doesn't unfold what you want.

**The workflow:** For equalities involving concrete values or function applications, try \`simpl\` followed by \`reflexivity\`. Often \`reflexivity\` alone suffices.

**Your task:** Prove that \`(fun x => x + 1) 3 = 4\`. Coq needs to beta-reduce the function application and compute the addition.`,
    exercise: {
      prelude: 'Require Import Arith.',
      template: `Theorem computation_example :\n  (fun x => x + 1) 3 = 4.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem computation_example :\n  (fun x => x + 1) 3 = 4.\nProof.\n  simpl.\n  reflexivity.\nQed.`,
    },
    successMessage: 'Coq verified the computation automatically. For concrete values, simpl + reflexivity (or just reflexivity) handles everything.',
    hint: 'simpl. reflexivity. (or just: reflexivity.)',
  },
  {
    id: 4,
    title: 'Rewriting with Equalities',
    explanation: `**\`rewrite\`** is one of the most important tactics. When you have a hypothesis \`H : a = b\`, then:

- \`rewrite H.\` replaces all occurrences of \`a\` with \`b\` in the goal
- \`rewrite <- H.\` replaces \`b\` with \`a\` (reverse direction)

You can chain multiple rewrites: \`rewrite H1. rewrite H2.\` or even \`rewrite H1, H2.\`

**When to use rewrite vs. apply:** Use \`rewrite\` when you have an equation and want to substitute. Use \`apply\` when you have an implication and want to use it to transform the goal.

**Your task:** Given that \`n = m\` and \`m = p\`, prove that \`n = p\`. You need to rewrite using both hypotheses to make both sides match.`,
    exercise: {
      prelude: '(* No imports needed *)',
      template: `Theorem eq_trans_manual : forall n m p : nat,\n  n = m -> m = p -> n = p.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem eq_trans_manual : forall n m p : nat,\n  n = m -> m = p -> n = p.\nProof.\n  intros n m p H1 H2.\n  rewrite H1.\n  exact H2.\nQed.`,
    },
    successMessage: '"rewrite H1" replaced n with m in the goal, changing "n = p" to "m = p". Then H2 was exactly what we needed.',
    hint: 'intros n m p H1 H2. rewrite H1. exact H2.',
  },
  {
    id: 5,
    title: 'Induction on Natural Numbers',
    explanation: `**Induction** is the core technique for proving properties about recursively-defined data. For natural numbers, \`induction n\` creates two subgoals:

**Base case** (\`n = 0\`): Prove the property holds for zero.
**Inductive step** (\`n = S n'\`): Assuming the property holds for \`n'\` (the **induction hypothesis**, usually named \`IHn'\`), prove it for \`S n'\`.

The typical workflow is:
1. \`intros\` the variables
2. \`induction n as [| n' IHn']\` (names the predecessor \`n'\` and hypothesis \`IHn'\`)
3. Prove the base case (often \`simpl. reflexivity.\`)
4. Prove the inductive step (often \`simpl. rewrite IHn'. reflexivity.\`)

**Your task:** Prove that \`n + 0 = n\`. This requires induction because \`+\` is defined by recursion on the first argument, so \`n + 0\` doesn't simplify without knowing what \`n\` is.`,
    exercise: {
      prelude: 'Require Import Arith.',
      template: `Theorem plus_n_O : forall n : nat, n + 0 = n.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem plus_n_O : forall n : nat, n + 0 = n.\nProof.\n  intros n.\n  induction n as [| n' IHn'].\n  - simpl. reflexivity.\n  - simpl. rewrite IHn'. reflexivity.\nQed.`,
    },
    successMessage: 'This is a classic Coq proof! The base case was trivial, and in the inductive step, "simpl" reduced "S n\' + 0" to "S (n\' + 0)", then "rewrite IHn\'" turned it into "S n\'" which matched the goal.',
    hint: 'induction n as [| n\' IHn\']. - simpl. reflexivity. - simpl. rewrite IHn\'. reflexivity.',
  },
  {
    id: 6,
    title: 'Induction on Lists',
    explanation: `Lists in Coq are defined inductively: a list is either \`[]\` (nil) or \`x :: l\` (cons of head \`x\` and tail \`l\`). Induction on lists works just like natural numbers:

**Base case** (\`l = []\`): Prove the property for the empty list.
**Inductive step** (\`l = x :: l'\`): Assuming the property holds for \`l'\`, prove it for \`x :: l'\`.

Use \`induction l as [| x l' IHl']\` to get names for the head \`x\`, tail \`l'\`, and hypothesis \`IHl'\`.

Common list functions: \`app\` (written \`++\`) for append, \`length\`, \`rev\` for reverse, \`map\`, \`filter\`. Most of their properties require induction on the list argument.

**Your task:** Prove that \`[] ++ l = l\` (easy, by computation) and \`l ++ [] = l\` (requires induction). We'll do the induction version.`,
    exercise: {
      prelude: 'Require Import List.\nImport ListNotations.',
      template: `Theorem app_nil_r : forall (A : Type) (l : list A),\n  l ++ [] = l.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem app_nil_r : forall (A : Type) (l : list A),\n  l ++ [] = l.\nProof.\n  intros A l.\n  induction l as [| x l' IHl'].\n  - simpl. reflexivity.\n  - simpl. rewrite IHl'. reflexivity.\nQed.`,
    },
    successMessage: 'The pattern is identical to natural number induction: base case is trivial, inductive step uses simpl + rewrite with the IH. This pattern will serve you well for many list proofs.',
    hint: 'induction l as [| x l\' IHl\']. - simpl. reflexivity. - simpl. rewrite IHl\'. reflexivity.',
  },
  {
    id: 7,
    title: 'Existential Proofs',
    explanation: `To prove \`exists x, P x\`, you need to provide a **witness** — a specific value of \`x\` — and then show it satisfies \`P\`. The \`exists\` tactic does this:

\`exists 42.\` provides 42 as the witness, changing the goal from \`exists x, P x\` to \`P 42\`.

To **use** an existential hypothesis \`H : exists x, P x\`, use \`destruct H as [x Hx]\` to extract the witness \`x\` and proof \`Hx : P x\`.

**Choosing the right witness** is the key challenge. Unlike other tactics where Coq can search, with \`exists\` you must provide the answer.

**Your task:** Prove that there exists a natural number whose successor is 3. Think about which number works, provide it as a witness, then let Coq verify.`,
    exercise: {
      prelude: 'Require Import Arith.',
      template: `Theorem exists_pred_of_3 : exists n : nat, S n = 3.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem exists_pred_of_3 : exists n : nat, S n = 3.\nProof.\n  exists 2.\n  reflexivity.\nQed.`,
    },
    successMessage: 'You provided the witness 2, and Coq verified that S 2 = 3. Existential proofs always follow this pattern: provide a witness, then verify.',
    hint: 'exists 2. reflexivity.',
  },
  {
    id: 8,
    title: 'Combining Techniques',
    explanation: `Now let's put everything together in a more involved proof. You'll need to use multiple techniques: \`intros\`, \`destruct\`, \`induction\`, \`simpl\`, \`rewrite\`, and \`reflexivity\`.

**Proof strategy tips:**
- Read the goal carefully before choosing a tactic
- If the goal has \`forall\` or \`->\`, use \`intros\`
- If you have a conjunction \`/\\\` hypothesis, \`destruct\` it
- If the goal involves recursively-defined functions on nat or list, consider \`induction\`
- If the goal is an equality with computable terms, try \`simpl\` then \`reflexivity\`
- If you have an equality hypothesis, \`rewrite\` with it
- **Step through one tactic at a time** to see what changed

**Your task:** Prove that addition is associative: \`(a + b) + c = a + (b + c)\`. This requires induction on \`a\`, with \`simpl\` and \`rewrite\` in the inductive step.`,
    exercise: {
      prelude: 'Require Import Arith.',
      template: `Theorem plus_assoc : forall a b c : nat,\n  (a + b) + c = a + (b + c).\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem plus_assoc : forall a b c : nat,\n  (a + b) + c = a + (b + c).\nProof.\n  intros a b c.\n  induction a as [| a' IHa'].\n  - simpl. reflexivity.\n  - simpl. rewrite IHa'. reflexivity.\nQed.`,
    },
    successMessage: 'Congratulations! You proved associativity of addition — a classic theorem from Software Foundations. You now have the core techniques to tackle any problem on LeetMethods. Head to the Problems page and start proving!',
    hint: 'induction a as [| a\' IHa\']. - simpl. reflexivity. - simpl. rewrite IHa\'. reflexivity.',
  },
];
