/**
 * @module TacticPlayground
 *
 * Interactive Coq code playground for experimenting with tactics.
 *
 * This component provides a sandbox environment where users can select
 * pre-defined exercises, edit Coq code in a CodeMirror editor, and
 * optionally view solutions. It is designed as a low-pressure learning
 * tool -- unlike the problem solver, it does not verify proofs or track
 * completion.
 *
 * Features:
 *   - Exercise selector buttons at the top for quick switching
 *   - Exercise info card showing title, associated tactic, and description
 *   - CodeMirror-based Coq editor with syntax highlighting
 *   - Show/hide solution toggle and reset button
 *
 * Design decisions:
 *   - The editor is a standalone `CoqEditor` without the full `useCoqSession`
 *     hook, so no actual Coq verification happens here. This is intentional:
 *     the playground is for reading/writing code, not running proofs.
 *   - Selecting a new exercise resets both the code and the solution visibility,
 *     preventing confusion from seeing a solution for a different exercise.
 *   - The exercises come from `playgroundExercises` in `src/lib/coq/playground-exercises.ts`,
 *     a static array of exercise objects with templates and solutions.
 */
'use client';

import { useState } from 'react';
import { Card } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import { CoqEditor } from '@/components/editor/CoqEditor';
import { playgroundExercises, type PlaygroundExercise } from '@/lib/coq/playground-exercises';

/**
 * Renders the Tactic Playground with exercise selection, a code editor,
 * and solution reveal controls.
 *
 * @returns The complete playground UI.
 */
export function TacticPlayground() {
  /** Currently selected exercise (defaults to the first exercise) */
  const [selectedExercise, setSelectedExercise] = useState<PlaygroundExercise>(playgroundExercises[0]);
  /** Current editor content, initialized from the selected exercise's template */
  const [code, setCode] = useState(selectedExercise.template);
  /** Whether the solution is currently visible */
  const [showSolution, setShowSolution] = useState(false);

  /**
   * Handles switching to a different exercise.
   * Resets the editor content to the new exercise's template and hides
   * any previously shown solution to avoid cross-exercise confusion.
   *
   * @param exercise - The newly selected exercise.
   */
  const handleSelectExercise = (exercise: PlaygroundExercise) => {
    setSelectedExercise(exercise);
    setCode(exercise.template);
    setShowSolution(false);
  };

  return (
    <div className="space-y-4">
      {/* Exercise selector -- horizontal row of toggle-style buttons.
          The active exercise gets primary coloring for visual distinction. */}
      <div className="flex flex-wrap gap-2">
        {playgroundExercises.map((ex) => (
          <button
            key={ex.id}
            onClick={() => handleSelectExercise(ex)}
            className={`px-3 py-1.5 text-sm rounded-md border transition-colors ${
              selectedExercise.id === ex.id
                ? 'bg-primary text-primary-foreground'
                : 'hover:bg-muted'
            }`}
          >
            {ex.title}
          </button>
        ))}
      </div>

      {/* Exercise info card -- shows the exercise title, which tactic it
          practices, and a text description of what to do */}
      <Card className="p-4">
        <div className="flex items-center gap-2 mb-2">
          <h3 className="font-semibold">{selectedExercise.title}</h3>
          {/* Tactic badge in monospace to visually match how tactics appear in code */}
          <Badge variant="secondary" className="text-xs font-mono">{selectedExercise.tactic}</Badge>
        </div>
        <p className="text-sm text-muted-foreground">{selectedExercise.description}</p>
      </Card>

      {/* CoqEditor instance -- a read/write code editor with Coq syntax highlighting.
          Fixed height of 250px to keep the playground compact on the Learn page.
          Note: This editor does NOT connect to jsCoq for verification; it is
          purely for code editing and reading. */}
      <div className="h-[250px] border rounded-md overflow-hidden">
        <CoqEditor
          value={code}
          onChange={setCode}
          className="h-full"
        />
      </div>

      {/* Control buttons: toggle solution visibility and reset code to template */}
      <div className="flex gap-2">
        <button
          onClick={() => setShowSolution(!showSolution)}
          className="text-sm text-primary hover:underline"
        >
          {showSolution ? 'Hide Solution' : 'Show Solution'}
        </button>
        <button
          onClick={() => {
            setCode(selectedExercise.template);
            setShowSolution(false);
          }}
          className="text-sm text-muted-foreground hover:underline"
        >
          Reset
        </button>
      </div>

      {/* Solution code block -- only visible when showSolution is true.
          Displayed in a monospace pre/code block with horizontal scroll
          for long lines. */}
      {showSolution && (
        <pre className="text-sm font-mono bg-muted p-4 rounded-md overflow-x-auto">
          <code>{selectedExercise.solution}</code>
        </pre>
      )}
    </div>
  );
}
