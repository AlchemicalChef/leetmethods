'use client';

import { useState } from 'react';
import { Lightbulb, ChevronDown, ChevronRight } from 'lucide-react';
import { Badge } from '@/components/ui/badge';
import type { TacticSuggestion, Confidence } from '@/lib/coq/tactic-suggester';

interface GuidedProofPanelProps {
  suggestions: TacticSuggestion[];
}

const confidenceColors: Record<Confidence, string> = {
  high: 'bg-green-100 text-green-800 dark:bg-green-900 dark:text-green-200',
  medium: 'bg-amber-100 text-amber-800 dark:bg-amber-900 dark:text-amber-200',
  low: 'bg-gray-100 text-gray-800 dark:bg-gray-900 dark:text-gray-200',
};

export function GuidedProofPanel({ suggestions }: GuidedProofPanelProps) {
  if (suggestions.length === 0) return null;

  return (
    <div className="border-t bg-amber-50/30 dark:bg-amber-950/10">
      <div className="flex items-center gap-1.5 px-3 py-1.5 text-xs font-medium text-amber-700 dark:text-amber-400">
        <Lightbulb className="h-3.5 w-3.5" />
        Guided Suggestions
      </div>
      <div className="px-3 pb-3 space-y-2">
        {suggestions.map((suggestion) => (
          <SuggestionCard key={suggestion.tactic} suggestion={suggestion} />
        ))}
      </div>
    </div>
  );
}

function SuggestionCard({ suggestion }: { suggestion: TacticSuggestion }) {
  const [expanded, setExpanded] = useState(false);

  return (
    <div className="rounded-md border bg-background/80 text-sm">
      <div className="px-3 py-2 flex items-start gap-2">
        <code className="font-mono font-medium text-primary shrink-0">{suggestion.tactic}</code>
        <span className="text-muted-foreground flex-1">{suggestion.reason}</span>
        <Badge className={`shrink-0 text-[10px] px-1.5 ${confidenceColors[suggestion.confidence]}`}>
          {suggestion.confidence}
        </Badge>
      </div>
      {suggestion.doc && (
        <>
          <button
            onClick={() => setExpanded(!expanded)}
            className="flex items-center gap-1 px-3 pb-2 text-xs text-muted-foreground hover:text-foreground transition-colors"
          >
            {expanded ? <ChevronDown className="h-3 w-3" /> : <ChevronRight className="h-3 w-3" />}
            Details
          </button>
          {expanded && (
            <div className="px-3 pb-3 border-t pt-2 space-y-1.5 text-xs">
              <div className="font-mono text-muted-foreground">{suggestion.doc.signature}</div>
              <pre className="bg-muted p-2 rounded text-[11px] overflow-x-auto whitespace-pre-wrap">
                {suggestion.doc.example}
              </pre>
            </div>
          )}
        </>
      )}
    </div>
  );
}
