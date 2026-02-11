# LeetMethods

A LeetCode-style platform for practicing formal proofs in Coq. Solve proof problems interactively in the browser, learn tactics through guided tutorials, and build long-term retention with spaced repetition.

## Features

- **Interactive Coq Proofs** -- Write and verify Coq proofs directly in the browser using jsCoq, with real-time goal display and error feedback
- **Problem Library** -- Curated problems across logic, induction, lists, arithmetic, data structures, and relations, each with hints, difficulty ratings, and prerequisite tracking
- **Tutorial System** -- Progressive tutorials based on the Software Foundations curriculum (Logical Foundations, Programming Language Foundations, Verified Functional Algorithms)
- **Spaced Repetition** -- SM-2 algorithm schedules reviews of completed problems to build lasting understanding
- **Learning Paths** -- Structured sequences of problems with prerequisite tracking and progress visualization
- **Achievements** -- Milestone, mastery, skill, and dedication badges for reaching learning goals
- **Custom Problems** -- Create and solve your own proof problems
- **Dark Mode** -- Full light/dark theme support
- **Fully Client-Side** -- No backend, no accounts, no data collection. All progress is stored in your browser's localStorage

## Tech Stack

- [Next.js 14](https://nextjs.org/) (App Router)
- [React 18](https://react.dev/)
- [TypeScript](https://www.typescriptlang.org/)
- [Tailwind CSS](https://tailwindcss.com/)
- [CodeMirror 6](https://codemirror.net/) with custom Coq syntax highlighting
- [jsCoq 0.17.1](https://github.com/jscoq/jscoq) (runs in an isolated iframe)
- [Zustand](https://github.com/pmndrs/zustand) for state management
- [Radix UI](https://www.radix-ui.com/) primitives
- [Vitest](https://vitest.dev/) + [Playwright](https://playwright.dev/) for testing

## Getting Started

### Prerequisites

- Node.js 18+
- npm

### Installation

```bash
git clone https://github.com/your-username/leetmethods.git
cd leetmethods
npm install
```

### Development

```bash
npm run dev
```

Open [http://localhost:3000](http://localhost:3000).

### Other Commands

```bash
npm run build          # Production build
npm run lint           # ESLint
npm test               # Run all unit tests
npm run test:watch     # Watch mode
npm run test:coverage  # Tests with coverage report
npm run type-check     # TypeScript type checking
npm run test:e2e       # Playwright end-to-end tests
```

## Project Structure

```
src/
  app/                    # Next.js App Router pages
    learn/                # Learning paths hub
    problems/             # Problem browser and solver
      [slug]/             # Individual problem page
      custom/             # Custom problem creation/solving
    stats/                # Progress statistics and SRS reviews
    tutorial/             # Tutorial hub and dynamic tutorial pages
      [slug]/             # Individual tutorial page
  components/
    editor/               # CoqEditor, GoalsPanel, EditorToolbar
    learn/                # Learning path cards and progress
    problem/              # ProblemSolver, ProblemList, descriptions
    stats/                # Stats overview, review section, achievements
    tutorial/             # Tutorial page component
    ui/                   # Shared UI primitives (Card, Badge, Dialog, etc.)
  content/
    problems/             # Problem JSON files by category
  hooks/                  # React hooks (useCoqSession, useAchievementChecker)
  lib/
    coq/                  # CoqService, parser, verifier, syntax, autocomplete
    paths/                # Learning paths definitions and progress
    prerequisites/        # Concept prerequisite graph
    problems/             # Problem loader and types
    srs/                  # SM-2 spaced repetition algorithm
    tutorial/             # Tutorial step definitions and registry
  store/                  # Zustand stores (progress, editor, achievements, etc.)
public/
  coq-worker.html         # Isolated iframe for jsCoq execution
  jscoq/                  # jsCoq 0.17.1 runtime files
```

## Architecture

LeetMethods is entirely client-side. jsCoq runs inside a hidden iframe to avoid state machine conflicts with Next.js, communicating via `postMessage`. A singleton `CoqService` manages the iframe lifecycle and persists across page navigations to avoid expensive re-initialization.

State is managed by five Zustand stores, four of which persist to localStorage with safe error handling and schema migrations.

For full architectural details, see [CLAUDE.md](./CLAUDE.md).

## License

[MIT](./LICENSE)
