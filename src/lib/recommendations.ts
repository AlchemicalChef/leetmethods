import type { ProblemSummary, Difficulty } from '@/lib/problems/types';

const difficultyOrder: Record<Difficulty, number> = { easy: 0, medium: 1, hard: 2 };

export function getNextRecommendation(
  currentProblem: ProblemSummary,
  allProblems: ProblemSummary[],
  completedSlugs: string[],
  dueSlugs?: string[]
): ProblemSummary | null {
  // Priority 0: Suggest due reviews before new problems
  if (dueSlugs && dueSlugs.length > 0) {
    const dueReview = allProblems.find((p) => dueSlugs.includes(p.slug) && p.slug !== currentProblem.slug);
    if (dueReview) return dueReview;
  }

  const completed = new Set(completedSlugs);
  const unsolved = allProblems.filter((p) => !completed.has(p.slug) && p.slug !== currentProblem.slug);

  if (unsolved.length === 0) return null;

  // Priority 1: Same category, same difficulty
  const sameCatSameDiff = unsolved.filter(
    (p) => p.category === currentProblem.category && p.difficulty === currentProblem.difficulty
  );
  if (sameCatSameDiff.length > 0) return sameCatSameDiff[0];

  // Priority 2: Same category, harder
  const sameCatHarder = unsolved
    .filter(
      (p) =>
        p.category === currentProblem.category &&
        difficultyOrder[p.difficulty] > difficultyOrder[currentProblem.difficulty]
    )
    .sort((a, b) => difficultyOrder[a.difficulty] - difficultyOrder[b.difficulty]);
  if (sameCatHarder.length > 0) return sameCatHarder[0];

  // Priority 3: Any same category
  const sameCat = unsolved.filter((p) => p.category === currentProblem.category);
  if (sameCat.length > 0) return sameCat[0];

  // Priority 4: Same difficulty, any category
  const sameDiff = unsolved.filter((p) => p.difficulty === currentProblem.difficulty);
  if (sameDiff.length > 0) return sameDiff[0];

  // Priority 5: Easiest unsolved
  return unsolved.sort((a, b) => difficultyOrder[a.difficulty] - difficultyOrder[b.difficulty])[0];
}
