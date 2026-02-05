# LeetMethods

A LeetCode-style platform for practicing Coq theorem proofs in the browser.

## Features

- **Browser-based Coq** - Write and verify proofs without installing anything
- **Real-time goals** - See proof state update as you apply tactics
- **10 curated problems** - Logic, induction, lists, and arithmetic
- **Progress tracking** - Solutions saved locally
- **Hint system** - Progressive hints when you're stuck

## Quick Start

```bash
npm install
npm run dev
```

Open [http://localhost:3000](http://localhost:3000)

## Tech Stack

- **Framework**: Next.js 14 (App Router)
- **Editor**: CodeMirror 6 with Coq syntax highlighting
- **State**: Zustand
- **Styling**: Tailwind CSS + shadcn/ui
- **Coq Runtime**: jsCoq (simulated for demo)

## Project Structure

```
src/
├── app/                    # Next.js pages
│   ├── problems/          # Problem list & solver
│   ├── learn/             # Learning resources
│   └── api/               # API routes
├── components/
│   ├── editor/            # CodeMirror, goals panel, toolbar
│   └── problem/           # Problem description, list, solver
├── lib/
│   ├── coq/               # Coq service, syntax, verifier
│   └── problems/          # Problem loader & types
├── store/                 # Zustand stores
└── content/problems/      # Problem JSON files
```

## Problems

| Category | Count | Difficulty |
|----------|-------|------------|
| Logic | 3 | Easy |
| Induction | 3 | Easy-Medium |
| Lists | 2 | Medium-Hard |
| Arithmetic | 2 | Medium-Hard |

## Scripts

```bash
npm run dev      # Start dev server
npm run build    # Production build
npm run start    # Start production server
npm run lint     # Run ESLint
```

## License

MIT
