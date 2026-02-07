'use client';

import Link from 'next/link';
import { Card } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import { ArrowRight } from 'lucide-react';
import { useProgressStore } from '@/store/progressStore';
import { computePathProgress } from '@/lib/paths/progress';
import type { LearningPath } from '@/lib/paths/types';
import { PATH_DIFFICULTY_COLORS } from '@/lib/ui-constants';

interface PathCardProps {
  path: LearningPath;
}

export function PathCard({ path }: PathCardProps) {
  const progress = useProgressStore((s) => s.progress);
  const pathProgress = computePathProgress(path, progress);

  const nextStep = pathProgress.nextStep !== null ? path.steps[pathProgress.nextStep] : null;
  const isComplete = pathProgress.completedSteps === pathProgress.totalSteps;

  return (
    <Link href={`/learn/${path.slug}`}>
      <Card className="p-4 h-full hover:bg-muted/50 transition-colors">
        <div className="flex items-start gap-3">
          <span className="text-2xl">{path.icon}</span>
          <div className="flex-1 min-w-0">
            <div className="flex items-center gap-2 mb-1 flex-wrap">
              <h3 className="font-semibold">{path.title}</h3>
              <Badge className={PATH_DIFFICULTY_COLORS[path.difficulty]}>
                {path.difficulty}
              </Badge>
            </div>
            <p className="text-sm text-muted-foreground mb-3">{path.description}</p>

            {/* Progress bar */}
            <div className="flex items-center gap-2 mb-2">
              <div className="flex-1 h-1.5 bg-muted rounded-full overflow-hidden">
                <div
                  className="h-full bg-primary rounded-full transition-all duration-500"
                  style={{ width: `${pathProgress.percent}%` }}
                />
              </div>
              <span className="text-xs text-muted-foreground">
                {pathProgress.completedSteps}/{pathProgress.totalSteps}
              </span>
            </div>

            {/* Continue link */}
            {isComplete ? (
              <span className="text-xs text-green-600 dark:text-green-400 font-medium">Completed</span>
            ) : nextStep ? (
              <span className="text-xs text-primary inline-flex items-center gap-1">
                Continue: {nextStep.title}
                <ArrowRight className="h-3 w-3" />
              </span>
            ) : null}
          </div>
        </div>
      </Card>
    </Link>
  );
}
