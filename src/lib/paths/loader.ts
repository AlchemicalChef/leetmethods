import { learningPaths } from './paths';
import type { LearningPath } from './types';

export function getAllPaths(): LearningPath[] {
  return learningPaths;
}

export function getPathBySlug(slug: string): LearningPath | null {
  return learningPaths.find((p) => p.slug === slug) ?? null;
}
