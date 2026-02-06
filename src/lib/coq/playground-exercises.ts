export interface PlaygroundExercise {
  id: string;
  title: string;
  tactic: string;
  description: string;
  prelude: string;
  template: string;
  solution: string;
}

export const playgroundExercises: PlaygroundExercise[] = [
  {
    id: 'try-intros',
    title: 'Try intros',
    tactic: 'intros',
    description: 'Use intros to move hypotheses from the goal into the context.',
    prelude: '',
    template: 'Goal forall (P Q : Prop), P -> Q -> P.\nProof.\n  (* Use intros to introduce P, Q, HP, HQ *)\nAdmitted.',
    solution: 'Goal forall (P Q : Prop), P -> Q -> P.\nProof.\n  intros P Q HP HQ.\n  exact HP.\nQed.',
  },
  {
    id: 'try-apply',
    title: 'Try apply',
    tactic: 'apply',
    description: 'Use apply to use a hypothesis that matches the goal.',
    prelude: '',
    template: 'Goal forall (P Q : Prop), (P -> Q) -> P -> Q.\nProof.\n  (* Use intros and apply *)\nAdmitted.',
    solution: 'Goal forall (P Q : Prop), (P -> Q) -> P -> Q.\nProof.\n  intros P Q HPQ HP.\n  apply HPQ.\n  exact HP.\nQed.',
  },
  {
    id: 'try-rewrite',
    title: 'Try rewrite',
    tactic: 'rewrite',
    description: 'Use rewrite to replace terms using an equality hypothesis.',
    prelude: '',
    template: 'Goal forall (n m : nat), n = m -> m = n.\nProof.\n  (* Use intros and rewrite *)\nAdmitted.',
    solution: 'Goal forall (n m : nat), n = m -> m = n.\nProof.\n  intros n m H.\n  rewrite H.\n  reflexivity.\nQed.',
  },
  {
    id: 'try-destruct',
    title: 'Try destruct',
    tactic: 'destruct',
    description: 'Use destruct to perform case analysis on a value.',
    prelude: '',
    template: 'Goal forall (b : bool), b = true \\/ b = false.\nProof.\n  (* Use intro and destruct b *)\nAdmitted.',
    solution: 'Goal forall (b : bool), b = true \\/ b = false.\nProof.\n  intro b.\n  destruct b.\n  - left. reflexivity.\n  - right. reflexivity.\nQed.',
  },
  {
    id: 'try-induction',
    title: 'Try induction',
    tactic: 'induction',
    description: 'Use induction to prove properties about natural numbers.',
    prelude: '',
    template: 'Goal forall n : nat, 0 + n = n.\nProof.\n  (* Use intro and simpl *)\nAdmitted.',
    solution: 'Goal forall n : nat, 0 + n = n.\nProof.\n  intro n.\n  simpl.\n  reflexivity.\nQed.',
  },
  {
    id: 'try-split',
    title: 'Try split',
    tactic: 'split',
    description: 'Use split to break a conjunction (P /\\ Q) into two subgoals.',
    prelude: '',
    template: 'Goal True /\\ True.\nProof.\n  (* Use split and exact I *)\nAdmitted.',
    solution: 'Goal True /\\ True.\nProof.\n  split.\n  - exact I.\n  - exact I.\nQed.',
  },
  {
    id: 'try-simpl',
    title: 'Try simpl',
    tactic: 'simpl',
    description: 'Use simpl to simplify/reduce computations in the goal.',
    prelude: 'Require Import Arith.',
    template: 'Goal 2 + 3 = 5.\nProof.\n  (* Use simpl and reflexivity *)\nAdmitted.',
    solution: 'Goal 2 + 3 = 5.\nProof.\n  simpl.\n  reflexivity.\nQed.',
  },
  {
    id: 'try-auto',
    title: 'Try auto',
    tactic: 'auto',
    description: 'Use auto to let Coq find a proof automatically.',
    prelude: '',
    template: 'Goal forall (P Q : Prop), P -> (P -> Q) -> Q.\nProof.\n  (* Just use auto *)\nAdmitted.',
    solution: 'Goal forall (P Q : Prop), P -> (P -> Q) -> Q.\nProof.\n  auto.\nQed.',
  },
];
