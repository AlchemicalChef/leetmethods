import type { ProblemProgress } from '@/lib/types/progress';
import type { LearningPath } from './types';

export interface PathProgress {
  completedSteps: number;
  totalSteps: number;
  percent: number;
  nextStep: number | null; // index of first incomplete step
}

export function computePathProgress(
  path: LearningPath,
  progress: Record<string, ProblemProgress>
): PathProgress {
  const totalSteps = path.steps.length;
  let completedSteps = 0;
  let nextStep: number | null = null;

  for (let i = 0; i < path.steps.length; i++) {
    if (progress[path.steps[i].problemSlug]?.completed) {
      completedSteps++;
    } else if (nextStep === null) {
      nextStep = i;
    }
  }

  return {
    completedSteps,
    totalSteps,
    percent: totalSteps > 0 ? Math.round((completedSteps / totalSteps) * 100) : 0,
    nextStep: completedSteps < totalSteps ? (nextStep ?? 0) : null,
  };
}
