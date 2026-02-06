'use client';

import { useState } from 'react';
import { Card } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import { CoqEditor } from '@/components/editor/CoqEditor';
import { playgroundExercises, type PlaygroundExercise } from '@/lib/coq/playground-exercises';

export function TacticPlayground() {
  const [selectedExercise, setSelectedExercise] = useState<PlaygroundExercise>(playgroundExercises[0]);
  const [code, setCode] = useState(selectedExercise.template);
  const [showSolution, setShowSolution] = useState(false);

  const handleSelectExercise = (exercise: PlaygroundExercise) => {
    setSelectedExercise(exercise);
    setCode(exercise.template);
    setShowSolution(false);
  };

  return (
    <div className="space-y-4">
      {/* Exercise selector */}
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

      {/* Exercise info */}
      <Card className="p-4">
        <div className="flex items-center gap-2 mb-2">
          <h3 className="font-semibold">{selectedExercise.title}</h3>
          <Badge variant="secondary" className="text-xs font-mono">{selectedExercise.tactic}</Badge>
        </div>
        <p className="text-sm text-muted-foreground">{selectedExercise.description}</p>
      </Card>

      {/* Editor */}
      <div className="h-[250px] border rounded-md overflow-hidden">
        <CoqEditor
          value={code}
          onChange={setCode}
          className="h-full"
        />
      </div>

      {/* Solution toggle */}
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

      {showSolution && (
        <pre className="text-sm font-mono bg-muted p-4 rounded-md overflow-x-auto">
          <code>{selectedExercise.solution}</code>
        </pre>
      )}
    </div>
  );
}
