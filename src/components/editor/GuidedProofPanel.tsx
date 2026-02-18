/**
 * @module GuidedProofPanel
 *
 * Displays context-aware tactic suggestions to help users complete Coq proofs.
 *
 * This component is part of the "guided mode" learning feature. When enabled,
 * it analyzes the current proof goals and suggests appropriate Coq tactics
 * with confidence levels and explanations. It appears below the goals in the
 * GoalsPanel.
 *
 * The suggestion system works as follows:
 * 1. The ProblemSolver computes suggestions via `suggestTactics()` whenever
 *    goals change and guided mode is active.
 * 2. Each suggestion includes a tactic name, a reason it might apply, a
 *    confidence level (high/medium/low), and optional documentation.
 * 3. Users can expand each suggestion to see the tactic signature and example.
 *
 * Design decisions:
 * - Confidence is color-coded (green/amber/gray) to help users prioritize.
 * - The panel uses amber/warm tones to visually distinguish it from the
 *   goal display (which uses primary/blue tones) and error messages (red).
 * - Documentation is hidden behind an expand toggle to keep the default
 *   view compact -- most users just need the tactic name and reason.
 *
 * @see {@link GoalsPanel} for the parent container
 * @see {@link suggestTactics} in `tactic-suggester.ts` for the suggestion engine
 */
'use client';

import { useState } from 'react';
import { Lightbulb, ChevronDown, ChevronRight } from 'lucide-react';
import { Badge } from '@/components/ui/badge';
import type { TacticSuggestion, Confidence } from '@/lib/coq/tactic-suggester';

/* ============================================================================
 * Types
 * ============================================================================ */

/**
 * Props for the GuidedProofPanel component.
 */
interface GuidedProofPanelProps {
  /** Array of tactic suggestions computed from the current proof goals */
  suggestions: TacticSuggestion[];
  /** Callback to insert a tactic at the editor cursor position */
  onInsertTactic?: (tactic: string) => void;
}

/* ============================================================================
 * Confidence Level Styling
 * ============================================================================ */

/**
 * Tailwind class mappings for each confidence level.
 * - **high**: Green -- the tactic is very likely to apply
 * - **medium**: Amber -- the tactic may apply depending on the exact goal shape
 * - **low**: Gray -- the tactic is a general suggestion, less certain
 */
const confidenceColors: Record<Confidence, string> = {
  high: 'bg-green-100 text-green-800 dark:bg-green-900 dark:text-green-200',
  medium: 'bg-amber-100 text-amber-800 dark:bg-amber-900 dark:text-amber-200',
  low: 'bg-gray-100 text-gray-800 dark:bg-gray-900 dark:text-gray-200',
};

/* ============================================================================
 * GuidedProofPanel Component
 * ============================================================================ */

/**
 * Panel showing tactic suggestions for the current proof state.
 *
 * Returns null when there are no suggestions (either guided mode is off
 * or no tactics match the current goals).
 *
 * @param props - See {@link GuidedProofPanelProps}
 * @returns The suggestions panel, or null if no suggestions available
 */
export function GuidedProofPanel({ suggestions, onInsertTactic }: GuidedProofPanelProps) {
  if (suggestions.length === 0) return null;

  return (
    <div className="border-t bg-amber-50/30 dark:bg-amber-950/10">
      {/* Section header with lightbulb icon */}
      <div className="flex items-center gap-1.5 px-3 py-1.5 text-xs font-medium text-amber-700 dark:text-amber-400">
        <Lightbulb className="h-3.5 w-3.5" />
        Guided Suggestions
      </div>
      {/* List of individual suggestion cards */}
      <div className="px-3 pb-3 space-y-2">
        {suggestions.map((suggestion) => (
          <SuggestionCard key={suggestion.tactic} suggestion={suggestion} onInsertTactic={onInsertTactic} />
        ))}
      </div>
    </div>
  );
}

/* ============================================================================
 * SuggestionCard Sub-component
 * ============================================================================ */

/**
 * Renders a single tactic suggestion with its name, reason, confidence badge,
 * and optionally expandable documentation (signature + example).
 *
 * @param props.suggestion - The tactic suggestion to display
 */
function SuggestionCard({ suggestion, onInsertTactic }: { suggestion: TacticSuggestion; onInsertTactic?: (tactic: string) => void }) {
  /** Whether the documentation section is expanded */
  const [expanded, setExpanded] = useState(false);

  return (
    <div className="rounded-md border bg-background/80 text-sm">
      {/* Main row: tactic name (clickable to insert), reason text, and confidence badge */}
      <div className="px-3 py-2 flex items-start gap-2">
        <button
          onClick={() => onInsertTactic?.(suggestion.tactic)}
          className="font-mono font-medium text-primary shrink-0 hover:underline cursor-pointer text-left"
          title="Click to insert at cursor"
        >
          {suggestion.tactic}
        </button>
        <span className="text-muted-foreground flex-1">{suggestion.reason}</span>
        <Badge className={`shrink-0 text-[10px] px-1.5 ${confidenceColors[suggestion.confidence]}`}>
          {suggestion.confidence}
        </Badge>
      </div>
      {/* Expandable documentation section -- only shown when doc data exists */}
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
              {/* Tactic signature in monospace */}
              <div className="font-mono text-muted-foreground">{suggestion.doc.signature}</div>
              {/* Usage example in a code block */}
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
