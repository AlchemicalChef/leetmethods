import { describe, it, expect } from 'vitest';
import { computePathProgress } from './progress';
import type { ProblemProgress } from '@/lib/types/progress';
import type { LearningPath, PathStep } from './types';
import { makeProgress } from '@/test/factories';

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function makeStep(slug: string): PathStep {
  return {
    problemSlug: slug,
    title: slug.replace(/-/g, ' '),
    description: `Description for ${slug}`,
  };
}

function makePath(slugs: string[], overrides: Partial<LearningPath> = {}): LearningPath {
  return {
    slug: 'test-path',
    title: 'Test Path',
    description: 'A path for testing',
    difficulty: 'beginner',
    icon: 'book',
    steps: slugs.map(makeStep),
    ...overrides,
  };
}

function progressMap(
  entries: ProblemProgress[]
): Record<string, ProblemProgress> {
  const map: Record<string, ProblemProgress> = {};
  for (const entry of entries) {
    map[entry.slug] = entry;
  }
  return map;
}

// ---------------------------------------------------------------------------
// computePathProgress
// ---------------------------------------------------------------------------

describe('computePathProgress', () => {
  it('returns 0% and nextStep=0 when no steps are completed', () => {
    const path = makePath(['p1', 'p2', 'p3']);
    const progress = progressMap([
      makeProgress('p1', false),
      makeProgress('p2', false),
      makeProgress('p3', false),
    ]);

    const result = computePathProgress(path, progress);

    expect(result.completedSteps).toBe(0);
    expect(result.totalSteps).toBe(3);
    expect(result.percent).toBe(0);
    expect(result.nextStep).toBe(0);
  });

  it('returns 100% and nextStep=null when all steps are completed', () => {
    const path = makePath(['p1', 'p2', 'p3']);
    const progress = progressMap([
      makeProgress('p1', true),
      makeProgress('p2', true),
      makeProgress('p3', true),
    ]);

    const result = computePathProgress(path, progress);

    expect(result.completedSteps).toBe(3);
    expect(result.totalSteps).toBe(3);
    expect(result.percent).toBe(100);
    expect(result.nextStep).toBeNull();
  });

  it('returns 50% and correct nextStep for 2 of 4 completed sequentially', () => {
    const path = makePath(['p1', 'p2', 'p3', 'p4']);
    const progress = progressMap([
      makeProgress('p1', true),
      makeProgress('p2', true),
      makeProgress('p3', false),
      makeProgress('p4', false),
    ]);

    const result = computePathProgress(path, progress);

    expect(result.completedSteps).toBe(2);
    expect(result.totalSteps).toBe(4);
    expect(result.percent).toBe(50);
    expect(result.nextStep).toBe(2);
  });

  it('points nextStep to the first incomplete step when completion is non-sequential', () => {
    const path = makePath(['p1', 'p2', 'p3', 'p4']);
    // Steps 0 and 2 completed, step 1 skipped
    const progress = progressMap([
      makeProgress('p1', true),
      makeProgress('p2', false),
      makeProgress('p3', true),
      makeProgress('p4', false),
    ]);

    const result = computePathProgress(path, progress);

    expect(result.completedSteps).toBe(2);
    expect(result.totalSteps).toBe(4);
    expect(result.percent).toBe(50);
    expect(result.nextStep).toBe(1);
  });

  it('returns totalSteps=0, percent=0, and nextStep=null for an empty path', () => {
    const path = makePath([]);
    const progress: Record<string, ProblemProgress> = {};

    const result = computePathProgress(path, progress);

    expect(result.completedSteps).toBe(0);
    expect(result.totalSteps).toBe(0);
    expect(result.percent).toBe(0);
    expect(result.nextStep).toBeNull();
  });

  it('returns 100% and nextStep=null for a single completed step', () => {
    const path = makePath(['p1']);
    const progress = progressMap([makeProgress('p1', true)]);

    const result = computePathProgress(path, progress);

    expect(result.completedSteps).toBe(1);
    expect(result.totalSteps).toBe(1);
    expect(result.percent).toBe(100);
    expect(result.nextStep).toBeNull();
  });

  it('returns 0% and nextStep=0 for a single incomplete step', () => {
    const path = makePath(['p1']);
    const progress = progressMap([makeProgress('p1', false)]);

    const result = computePathProgress(path, progress);

    expect(result.completedSteps).toBe(0);
    expect(result.totalSteps).toBe(1);
    expect(result.percent).toBe(0);
    expect(result.nextStep).toBe(0);
  });

  it('ignores progress entries for slugs not in the path', () => {
    const path = makePath(['p1', 'p2']);
    const progress = progressMap([
      makeProgress('p1', false),
      makeProgress('p2', false),
      makeProgress('unrelated-a', true),
      makeProgress('unrelated-b', true),
    ]);

    const result = computePathProgress(path, progress);

    expect(result.completedSteps).toBe(0);
    expect(result.totalSteps).toBe(2);
    expect(result.percent).toBe(0);
    expect(result.nextStep).toBe(0);
  });

  it('returns 75% and correct nextStep for 3 of 4 completed', () => {
    const path = makePath(['p1', 'p2', 'p3', 'p4']);
    const progress = progressMap([
      makeProgress('p1', true),
      makeProgress('p2', true),
      makeProgress('p3', false),
      makeProgress('p4', true),
    ]);

    const result = computePathProgress(path, progress);

    expect(result.completedSteps).toBe(3);
    expect(result.totalSteps).toBe(4);
    expect(result.percent).toBe(75);
    expect(result.nextStep).toBe(2);
  });

  it('treats missing progress entries as incomplete', () => {
    const path = makePath(['p1', 'p2', 'p3']);
    // Only p1 has a progress entry; p2 and p3 are absent from the record
    const progress = progressMap([makeProgress('p1', true)]);

    const result = computePathProgress(path, progress);

    expect(result.completedSteps).toBe(1);
    expect(result.totalSteps).toBe(3);
    expect(result.percent).toBe(33);
    expect(result.nextStep).toBe(1);
  });

  it('rounds percent correctly for non-integer percentages', () => {
    // 1/3 = 33.333... should round to 33
    const pathA = makePath(['p1', 'p2', 'p3']);
    const progressA = progressMap([makeProgress('p1', true)]);

    expect(computePathProgress(pathA, progressA).percent).toBe(33);

    // 2/3 = 66.666... should round to 67
    const pathB = makePath(['p1', 'p2', 'p3']);
    const progressB = progressMap([
      makeProgress('p1', true),
      makeProgress('p2', true),
    ]);

    expect(computePathProgress(pathB, progressB).percent).toBe(67);
  });
});
