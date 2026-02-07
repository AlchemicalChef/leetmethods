export interface TutorialStep {
  id: number;
  title: string;
  explanation: string;
  exercise: {
    prelude: string;
    template: string;
    solution: string;
  };
  successMessage: string;
  hint: string;
}

export const tutorialSteps: TutorialStep[] = [
  {
    id: 1,
    title: 'Welcome to Coq',
    explanation: `**What is Coq?** Coq is a proof assistant — a tool that lets you write mathematical proofs that a computer can verify.

In Coq, you state a theorem and then build a **proof** step by step using **tactics**. Each tactic transforms the current proof state until nothing remains to prove.

**Your first proof:** The simplest thing you can prove is \`True\`. In Coq, \`True\` is a proposition that is trivially provable using the \`exact I\` tactic (where \`I\` is the proof of \`True\`).

Try typing \`exact I.\` between \`Proof.\` and \`Admitted.\`, then click **Run** to execute all the code.`,
    exercise: {
      prelude: '(* No imports needed *)',
      template: `Theorem my_first_proof : True.\nProof.\n  (* Type: exact I. *)\nAdmitted.`,
      solution: `Theorem my_first_proof : True.\nProof.\n  exact I.\nQed.`,
    },
    successMessage: 'You proved your first theorem! The "No more goals" message means the proof is complete.',
    hint: 'Replace (* Type: exact I. *) with: exact I.',
  },
  {
    id: 2,
    title: 'Goals & Hypotheses',
    explanation: `**The Goals Panel** shows what you still need to prove. Each goal has:
- **Hypotheses** (above the line) — facts you can use
- **Conclusion** (below the line) — what you need to show

**Step-by-step execution:** Instead of running all code at once, you can step through one tactic at a time using the **Step Forward** button (or \`Alt+N\`). This lets you see how each tactic changes the proof state.

**Your task:** Prove \`P -> P\` (if P then P). Use \`intros H\` to move P from the goal into your hypotheses as \`H\`, then use \`exact H\` to finish.

Try stepping through one tactic at a time to see the goals change!`,
    exercise: {
      prelude: '(* No imports needed *)',
      template: `Theorem identity : forall P : Prop, P -> P.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem identity : forall P : Prop, P -> P.\nProof.\n  intros H.\n  exact H.\nQed.`,
    },
    successMessage: 'Great! You used "intros" to move a hypothesis into context and "exact" to prove the goal.',
    hint: 'Type: intros H. exact H. (each followed by a period)',
  },
  {
    id: 3,
    title: 'The intros Tactic',
    explanation: `**\`intros\`** is one of the most common tactics. It moves universally quantified variables and implications from the goal into your hypotheses.

For example, if the goal is \`forall A B : Prop, A -> B -> A\`, then:
- \`intros A B.\` introduces the propositions A and B
- \`intros HA HB.\` introduces the hypotheses A and B with names HA and HB

You can also combine them: \`intros A B HA HB.\` does it all at once.

**Your task:** Prove that \`A -> B -> A\`. Introduce all hypotheses, then use the right one.`,
    exercise: {
      prelude: '(* No imports needed *)',
      template: `Theorem first_arg : forall A B : Prop, A -> B -> A.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem first_arg : forall A B : Prop, A -> B -> A.\nProof.\n  intros A B HA HB.\n  exact HA.\nQed.`,
    },
    successMessage: 'Perfect! You can introduce multiple hypotheses at once and pick the right one to close the goal.',
    hint: 'Type: intros A B HA HB. exact HA.',
  },
  {
    id: 4,
    title: 'The apply Tactic',
    explanation: `**\`apply\`** uses a hypothesis or lemma to prove the current goal or reduce it to simpler goals.

If you have hypothesis \`H : A -> B\` and your goal is \`B\`, then \`apply H.\` changes the goal to \`A\` (you need to prove A to get B via H).

This is like **modus ponens** backwards: to prove the conclusion, prove the premise.

**Your task:** Prove modus ponens: if \`P -> Q\` and \`P\`, then \`Q\`. Use \`intros\` then \`apply\`.`,
    exercise: {
      prelude: '(* No imports needed *)',
      template: `Theorem modus_ponens : forall P Q : Prop, (P -> Q) -> P -> Q.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem modus_ponens : forall P Q : Prop, (P -> Q) -> P -> Q.\nProof.\n  intros P Q HPQ HP.\n  apply HPQ.\n  exact HP.\nQed.`,
    },
    successMessage: 'Excellent! "apply" is incredibly powerful — it lets you chain logical implications together.',
    hint: 'Type: intros P Q HPQ HP. apply HPQ. exact HP.',
  },
  {
    id: 5,
    title: 'Your First Real Proof',
    explanation: `Now let's combine everything! You'll use a new tactic: **\`split\`**.

When the goal is a conjunction \`A /\\ B\`, the \`split\` tactic breaks it into two separate goals: first prove \`A\`, then prove \`B\`.

**Your task:** Prove that if you have both \`P\` and \`Q\`, you can prove \`P /\\ Q\`. This requires:
1. \`intros\` to introduce hypotheses
2. \`split\` to break the conjunction
3. \`exact\` to close each subgoal

Step through the proof to see how \`split\` creates two goals!`,
    exercise: {
      prelude: '(* No imports needed *)',
      template: `Theorem and_intro : forall P Q : Prop, P -> Q -> P /\\ Q.\nProof.\n  (* Your proof here *)\nAdmitted.`,
      solution: `Theorem and_intro : forall P Q : Prop, P -> Q -> P /\\ Q.\nProof.\n  intros P Q HP HQ.\n  split.\n  - exact HP.\n  - exact HQ.\nQed.`,
    },
    successMessage: 'Congratulations! You completed the tutorial! You now know intros, exact, apply, and split — the building blocks of Coq proofs. Head to the Problems page to practice more!',
    hint: 'Type: intros P Q HP HQ. split. - exact HP. - exact HQ.',
  },
];
