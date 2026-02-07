'use client';

import Link from 'next/link';
import { Card } from '@/components/ui/card';
import { CheckCircle2, Circle, BookOpen, AlertTriangle } from 'lucide-react';
import type { PrerequisiteStatus } from '@/lib/prerequisites';

interface PrerequisitesPanelProps {
  status: PrerequisiteStatus;
}

export function PrerequisitesPanel({ status }: PrerequisitesPanelProps) {
  const { problemPrereqs, conceptPrereqs } = status;
  if (problemPrereqs.length === 0 && conceptPrereqs.length === 0) return null;

  return (
    <Card className="border-amber-200 dark:border-amber-800 bg-amber-50/50 dark:bg-amber-950/20 p-4">
      <div className="flex items-center gap-2 mb-3">
        <AlertTriangle className="h-4 w-4 text-amber-600 dark:text-amber-400" />
        <span className="font-medium text-amber-800 dark:text-amber-300">Prerequisites</span>
        {status.allSatisfied && (
          <span className="text-xs text-green-600 dark:text-green-400 ml-auto">All met</span>
        )}
      </div>

      {problemPrereqs.length > 0 && (
        <div className="space-y-1.5 mb-3">
          <span className="text-xs text-amber-700 dark:text-amber-400 font-medium">Problems</span>
          {problemPrereqs.map((p) => (
            <Link
              key={p.slug}
              href={`/problems/${p.slug}`}
              className="flex items-center gap-2 text-sm hover:underline"
            >
              {p.completed ? (
                <CheckCircle2 className="h-3.5 w-3.5 text-green-500 shrink-0" />
              ) : (
                <Circle className="h-3.5 w-3.5 text-amber-400 shrink-0" />
              )}
              <span className={p.completed ? 'text-muted-foreground line-through' : 'text-foreground'}>
                {p.title}
              </span>
            </Link>
          ))}
        </div>
      )}

      {conceptPrereqs.length > 0 && (
        <div className="space-y-1.5">
          <span className="text-xs text-amber-700 dark:text-amber-400 font-medium">Concepts</span>
          {conceptPrereqs.map((c) => (
            <Link
              key={c.id}
              href={c.learnPath.startsWith('/') ? c.learnPath : `/problems/${c.learnPath}`}
              className="flex items-center gap-2 text-sm hover:underline"
            >
              {c.satisfied ? (
                <CheckCircle2 className="h-3.5 w-3.5 text-green-500 shrink-0" />
              ) : (
                <BookOpen className="h-3.5 w-3.5 text-amber-400 shrink-0" />
              )}
              <span className={c.satisfied ? 'text-muted-foreground line-through' : 'text-foreground'}>
                {c.displayName}
              </span>
              {!c.satisfied && c.description && (
                <span className="text-xs text-muted-foreground hidden sm:inline">
                  - {c.description}
                </span>
              )}
            </Link>
          ))}
        </div>
      )}
    </Card>
  );
}
