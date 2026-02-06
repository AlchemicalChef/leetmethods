# LeetMethods

A LeetCode-style platform for practicing formal proofs in Coq. Solve proof challenges directly in your browser with real-time verification powered by jsCoq.

## Features

- **In-browser Coq verification** -- proofs are checked by the actual Coq proof assistant running client-side via jsCoq 0.17.1
- **10 built-in problems** across 4 categories (logic, induction, lists, arithmetic)
- **Interactive editor** with CodeMirror 6 and Coq syntax highlighting
- **Step-by-step execution** -- execute proofs one statement at a time or all at once
- **Live goals panel** -- see proof goals and hypotheses update as you step through
- **Forbidden tactic detection** -- prevents `admit`/`Admitted` and other disallowed shortcuts
- **Progress tracking** -- completion status, attempt counts, and hints persisted in local storage
- **Dark mode** support

## Tech Stack

- **Next.js 14** (App Router) + TypeScript
- **jsCoq 0.17.1** -- self-hosted Coq proof assistant (js_of_ocaml backend)
- **CodeMirror 6** -- editor with Coq syntax support
- **Tailwind CSS** + **shadcn/ui** -- styling and components
- **Zustand** -- state management

## Getting Started

```bash
npm install
npm run dev
```

Open [http://localhost:3000](http://localhost:3000) to start solving proofs.

## Project Structure

```
src/
  app/                    # Next.js App Router pages
    problems/[slug]/      # Individual problem pages
  components/
    editor/               # CoqEditor, GoalsPanel
    problem/              # ProblemSolver, ProblemDescription, EditorToolbar
    ui/                   # shadcn/ui components
  content/
    problems/             # Problem definitions (JSON)
      arithmetic/         # add-assoc, even-double
      induction/          # plus-n-zero, plus-comm, mult-n-zero
      lists/              # list-length-app, list-rev-rev
      logic/              # modus-ponens, double-negation, and-commutative
  lib/
    coq/                  # CoqService, types, verifier
    problems/             # Problem loader and types
  store/                  # Zustand stores (coqStore, progressStore)
public/
  coq-worker.html         # Iframe-isolated jsCoq runtime
  jscoq/                  # Self-hosted jsCoq assets
```

## Problems

| Category   | Problems                                    | Difficulty  |
|------------|---------------------------------------------|-------------|
| Logic      | Modus Ponens, Double Negation, AND Commutativity | Easy        |
| Induction  | Plus N Zero, Plus Commutativity, Mult N Zero | Easy-Medium |
| Lists      | List Length Append, List Rev Rev             | Medium-Hard |
| Arithmetic | Even Double, Addition Associativity          | Medium-Hard |

## Adding New Problems

### 1. Create the problem JSON file

Add a file to `src/content/problems/<category>/<slug>.json`:

```json
{
  "id": "11",
  "slug": "or-commutative",
  "title": "Disjunction is Commutative",
  "difficulty": "easy",
  "category": "logic",
  "tags": ["disjunction", "basic"],
  "description": "Prove that logical OR is commutative.\n\n**Goal:** `forall P Q : Prop, P \\/ Q -> Q \\/ P`",
  "hints": [
    "Use `intros` to introduce the propositions and hypothesis",
    "Use `destruct` on the disjunction to case-split",
    "Use `left` and `right` to choose which side to prove"
  ],
  "prelude": "(* No imports needed *)",
  "template": "Theorem or_commutative : forall P Q : Prop, P \\/ Q -> Q \\/ P.\nProof.\n  (* Your proof here *)\nAdmitted.",
  "solution": "Theorem or_commutative : forall P Q : Prop, P \\/ Q -> Q \\/ P.\nProof.\n  intros P Q H.\n  destruct H as [HP | HQ].\n  - right. exact HP.\n  - left. exact HQ.\nQed.",
  "forbiddenTactics": ["admit", "Admitted"]
}
```

### 2. Register it in the loader

Edit `src/lib/problems/loader.ts`:

```typescript
import orCommProblem from '@/content/problems/logic/or-commutative.json';

const problems: Problem[] = [
  // ...existing problems...
  orCommProblem as Problem,
];
```

### Field Reference

| Field              | Description                                                      |
|--------------------|------------------------------------------------------------------|
| `id`               | Unique numeric string                                            |
| `slug`             | URL-friendly identifier (used in `/problems/<slug>`)             |
| `title`            | Display name                                                     |
| `difficulty`       | `"easy"`, `"medium"`, or `"hard"`                                |
| `category`         | Folder name under `src/content/problems/`                        |
| `tags`             | Array of topic tags                                              |
| `description`      | Markdown-formatted problem description                           |
| `hints`            | Progressive hints revealed one at a time                         |
| `prelude`          | Coq code loaded before the user's code (imports, helper lemmas)  |
| `template`         | Starting code shown in the editor (should end with `Admitted.`)  |
| `solution`         | Reference solution (not shown to users)                          |
| `forbiddenTactics` | Tactics that are blocked (always include `admit` and `Admitted`) |

### Tips

- **prelude**: Use for `Require Import` statements and helper lemmas. Keep it minimal.
- **template**: Always end with `Admitted.` so the forbidden tactic check catches unmodified submissions.
- **Test your solution**: Paste the full `prelude + solution` into the app to verify it compiles.
- **Categories**: `logic`, `induction`, `lists`, `arithmetic`. Create new category folders as needed.

## Scripts

```bash
npm run dev      # Start dev server
npm run build    # Production build
npm run start    # Start production server
npm run lint     # Run ESLint
```

## Architecture

jsCoq runs inside a hidden iframe (`public/coq-worker.html`) to isolate it from the Next.js environment. The `CoqService` class in `src/lib/coq/CoqService.ts` communicates with the iframe via `postMessage`. This architecture avoids conflicts between jsCoq's internal state machine and Next.js's runtime, also i have great disdain for next.js

## License

MIT
