'use client';

import { useState } from 'react';
import { Badge } from '@/components/ui/badge';
import { Button } from '@/components/ui/button';
import { Card } from '@/components/ui/card';
import { ScrollArea } from '@/components/ui/scroll-area';
import { Separator } from '@/components/ui/separator';
import { ChevronDown, ChevronRight, Lightbulb, BookOpen, Eye } from 'lucide-react';
import type { Problem } from '@/lib/problems/types';
import type { PrerequisiteStatus } from '@/lib/prerequisites';
import { DIFFICULTY_COLORS } from '@/lib/ui-constants';
import { PrerequisitesPanel } from './PrerequisitesPanel';

interface ProblemDescriptionProps {
  problem: Problem;
  hintsRevealed: number;
  onRevealHint: () => void;
  solutionAvailable?: boolean;
  prerequisiteStatus?: PrerequisiteStatus;
  isCustom?: boolean;
  onEdit?: () => void;
  onDelete?: () => void;
  className?: string;
}

export function ProblemDescription({
  problem,
  hintsRevealed,
  onRevealHint,
  solutionAvailable = false,
  prerequisiteStatus,
  isCustom,
  onEdit,
  onDelete,
  className = '',
}: ProblemDescriptionProps) {
  const [showPrelude, setShowPrelude] = useState(false);

  return (
    <ScrollArea className={`h-full ${className}`}>
      <div className="p-6 space-y-6">
        {/* Title and metadata */}
        <div>
          <h1 className="text-2xl font-bold mb-3">{problem.title}</h1>
          <div className="flex flex-wrap gap-2 items-center">
            <Badge className={DIFFICULTY_COLORS[problem.difficulty]}>
              {problem.difficulty.charAt(0).toUpperCase() + problem.difficulty.slice(1)}
            </Badge>
            <Badge variant="outline">{problem.category}</Badge>
            {problem.tags.map((tag) => (
              <Badge key={tag} variant="secondary">
                {tag}
              </Badge>
            ))}
          </div>
        </div>

        {/* Custom problem actions */}
        {isCustom && (onEdit || onDelete) && (
          <div className="flex items-center gap-2">
            {onEdit && (
              <Button variant="outline" size="sm" onClick={onEdit}>
                Edit
              </Button>
            )}
            {onDelete && (
              <Button variant="outline" size="sm" onClick={onDelete} className="text-red-600 hover:text-red-700">
                Delete
              </Button>
            )}
          </div>
        )}

        {/* Prerequisites */}
        {prerequisiteStatus && (prerequisiteStatus.problemPrereqs.length > 0 || prerequisiteStatus.conceptPrereqs.length > 0) && (
          <PrerequisitesPanel status={prerequisiteStatus} />
        )}

        <Separator />

        {/* Description - FIX #2: Sanitize HTML to prevent XSS */}
        <div className="prose prose-sm dark:prose-invert max-w-none">
          <FormattedDescription text={problem.description} />
        </div>

        {/* Hints section */}
        {problem.hints.length > 0 && (
          <Card className="p-4">
            <div className="flex items-center gap-2 mb-3">
              <Lightbulb className="h-4 w-4 text-yellow-500" />
              <span className="font-medium">Hints</span>
              <span className="text-sm text-muted-foreground">
                ({hintsRevealed}/{problem.hints.length} revealed)
              </span>
            </div>

            <div className="space-y-2">
              {problem.hints.slice(0, hintsRevealed).map((hint, index) => (
                <div
                  key={index}
                  className="text-sm p-2 bg-muted/50 rounded border-l-2 border-yellow-400"
                >
                  <span className="font-medium text-muted-foreground">Hint {index + 1}:</span>{' '}
                  {hint}
                </div>
              ))}
            </div>

            {hintsRevealed < problem.hints.length && (
              <Button
                variant="ghost"
                size="sm"
                onClick={onRevealHint}
                className="mt-3"
              >
                <Lightbulb className="h-3 w-3 mr-1" />
                Show Hint {hintsRevealed + 1}
              </Button>
            )}
          </Card>
        )}

        {/* Prelude section */}
        {problem.prelude && (
          <Card className="overflow-hidden">
            <button
              onClick={() => setShowPrelude(!showPrelude)}
              aria-label={showPrelude ? 'Hide prelude code' : 'Show prelude code'}
              className="w-full flex items-center gap-2 p-3 hover:bg-muted/50 transition-colors"
            >
              {showPrelude ? (
                <ChevronDown className="h-4 w-4" />
              ) : (
                <ChevronRight className="h-4 w-4" />
              )}
              <BookOpen className="h-4 w-4 text-muted-foreground" />
              <span className="font-medium">Prelude</span>
              <span className="text-sm text-muted-foreground">(read-only imports/definitions)</span>
            </button>

            {showPrelude && (
              <div className="border-t bg-muted/20">
                <pre className="p-4 text-sm font-mono overflow-x-auto">
                  <code>{problem.prelude}</code>
                </pre>
              </div>
            )}
          </Card>
        )}

        {/* Solution reveal */}
        {solutionAvailable && problem.solution && (
          <SolutionReveal solution={problem.solution} />
        )}
      </div>
    </ScrollArea>
  );
}

function SolutionReveal({ solution }: { solution: string }) {
  const [confirmed, setConfirmed] = useState(false);
  const [expanded, setExpanded] = useState(false);

  if (!confirmed) {
    return (
      <Card className="border-amber-200 dark:border-amber-800 bg-amber-50/50 dark:bg-amber-950/20 p-4">
        <div className="flex items-center gap-2 mb-2">
          <Eye className="h-4 w-4 text-amber-600 dark:text-amber-400" />
          <span className="font-medium text-amber-800 dark:text-amber-300">Reference Solution</span>
        </div>
        <p className="text-sm text-amber-700 dark:text-amber-400 mb-3">
          Are you sure you want to see the solution? Try solving it yourself first!
        </p>
        <Button
          variant="outline"
          size="sm"
          onClick={() => setConfirmed(true)}
          className="border-amber-300 dark:border-amber-700 text-amber-800 dark:text-amber-300 hover:bg-amber-100 dark:hover:bg-amber-900/30"
        >
          <Eye className="h-3 w-3 mr-1" />
          Show Solution
        </Button>
      </Card>
    );
  }

  return (
    <Card className="border-amber-200 dark:border-amber-800 overflow-hidden">
      <button
        onClick={() => setExpanded(!expanded)}
        aria-label={expanded ? 'Hide reference solution' : 'Show reference solution'}
        className="w-full flex items-center gap-2 p-3 hover:bg-amber-50/50 dark:hover:bg-amber-950/20 transition-colors"
      >
        {expanded ? (
          <ChevronDown className="h-4 w-4 text-amber-600" />
        ) : (
          <ChevronRight className="h-4 w-4 text-amber-600" />
        )}
        <Eye className="h-4 w-4 text-amber-600 dark:text-amber-400" />
        <span className="font-medium text-amber-800 dark:text-amber-300">Reference Solution</span>
      </button>
      {expanded && (
        <div className="border-t border-amber-200 dark:border-amber-800 bg-muted/20">
          <pre className="p-4 text-sm font-mono overflow-x-auto">
            <code>{solution}</code>
          </pre>
        </div>
      )}
    </Card>
  );
}

// FIX #2: Safe markdown-like formatting without dangerouslySetInnerHTML
// This approach uses React components instead of raw HTML
function FormattedDescription({ text }: { text: string }) {
  const lines = text.split('\n');
  const elements: React.ReactNode[] = [];
  let currentParagraph: React.ReactNode[] = [];
  let inCodeBlock = false;
  let codeBlockContent: string[] = [];
  let codeBlockLang = '';
  let key = 0;

  const flushParagraph = () => {
    if (currentParagraph.length > 0) {
      elements.push(<p key={key++}>{currentParagraph}</p>);
      currentParagraph = [];
    }
  };

  // Use a ref counter to ensure unique keys across all inline elements
  let inlineKeyCounter = 0;

  const formatInlineText = (line: string): React.ReactNode[] => {
    const result: React.ReactNode[] = [];
    let remaining = line;

    while (remaining.length > 0) {
      // Bold
      const boldMatch = remaining.match(/^\*\*(.+?)\*\*/);
      if (boldMatch) {
        result.push(<strong key={`inline-${inlineKeyCounter++}`}>{boldMatch[1]}</strong>);
        remaining = remaining.slice(boldMatch[0].length);
        continue;
      }

      // Italic
      const italicMatch = remaining.match(/^\*(.+?)\*/);
      if (italicMatch) {
        result.push(<em key={`inline-${inlineKeyCounter++}`}>{italicMatch[1]}</em>);
        remaining = remaining.slice(italicMatch[0].length);
        continue;
      }

      // Inline code
      const codeMatch = remaining.match(/^`([^`]+)`/);
      if (codeMatch) {
        result.push(
          <code key={`inline-${inlineKeyCounter++}`} className="bg-muted px-1 py-0.5 rounded text-sm font-mono">
            {codeMatch[1]}
          </code>
        );
        remaining = remaining.slice(codeMatch[0].length);
        continue;
      }

      // Regular text - find next special character or end
      const nextSpecial = remaining.search(/\*|`/);
      if (nextSpecial === -1) {
        result.push(<span key={`inline-${inlineKeyCounter++}`}>{remaining}</span>);
        break;
      } else if (nextSpecial === 0) {
        // Special char that didn't match patterns, add as text
        result.push(<span key={`inline-${inlineKeyCounter++}`}>{remaining[0]}</span>);
        remaining = remaining.slice(1);
      } else {
        result.push(<span key={`inline-${inlineKeyCounter++}`}>{remaining.slice(0, nextSpecial)}</span>);
        remaining = remaining.slice(nextSpecial);
      }
    }

    return result;
  };

  for (const line of lines) {
    // Code block start/end
    if (line.startsWith('```')) {
      if (!inCodeBlock) {
        flushParagraph();
        inCodeBlock = true;
        codeBlockLang = line.slice(3).trim();
        codeBlockContent = [];
      } else {
        elements.push(
          <pre key={key++} className="bg-muted p-4 rounded-md overflow-x-auto">
            <code className={codeBlockLang ? `language-${codeBlockLang}` : ''}>
              {codeBlockContent.join('\n')}
            </code>
          </pre>
        );
        inCodeBlock = false;
        codeBlockContent = [];
        codeBlockLang = '';
      }
      continue;
    }

    if (inCodeBlock) {
      codeBlockContent.push(line);
      continue;
    }

    // Headers
    if (line.startsWith('### ')) {
      flushParagraph();
      elements.push(<h3 key={key++} className="text-lg font-semibold mt-4 mb-2">{line.slice(4)}</h3>);
      continue;
    }
    if (line.startsWith('## ')) {
      flushParagraph();
      elements.push(<h2 key={key++} className="text-xl font-semibold mt-4 mb-2">{line.slice(3)}</h2>);
      continue;
    }
    if (line.startsWith('# ')) {
      flushParagraph();
      elements.push(<h1 key={key++} className="text-2xl font-bold mt-4 mb-2">{line.slice(2)}</h1>);
      continue;
    }

    // Empty line = paragraph break
    if (line.trim() === '') {
      flushParagraph();
      continue;
    }

    // Regular text with inline formatting
    if (currentParagraph.length > 0) {
      currentParagraph.push(' ');
    }
    currentParagraph.push(...formatInlineText(line));
  }

  // Flush any remaining content
  flushParagraph();

  return <>{elements}</>;
}
