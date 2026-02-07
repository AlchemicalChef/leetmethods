'use client';

import { Badge } from '@/components/ui/badge';
import { AlertTriangle } from 'lucide-react';

interface PrerequisitesBadgeProps {
  unsatisfiedCount: number;
}

export function PrerequisitesBadge({ unsatisfiedCount }: PrerequisitesBadgeProps) {
  if (unsatisfiedCount === 0) return null;

  return (
    <Badge
      variant="outline"
      className="bg-amber-50 text-amber-700 border-amber-200 dark:bg-amber-950/30 dark:text-amber-400 dark:border-amber-800"
    >
      <AlertTriangle className="h-3 w-3 mr-1" />
      {unsatisfiedCount} prereq{unsatisfiedCount !== 1 ? 's' : ''}
    </Badge>
  );
}
