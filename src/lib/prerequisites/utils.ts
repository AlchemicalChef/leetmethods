import type { Problem } from '@/lib/problems/types';
import { conceptMap } from './concepts';
import type { ConceptInfo } from './concepts';

export interface ProblemPrereq {
  slug: string;
  title: string;
  completed: boolean;
}

export interface ConceptPrereq {
  id: string;
  displayName: string;
  description: string;
  satisfied: boolean;
  learnPath: string;
}

export interface PrerequisiteStatus {
  problemPrereqs: ProblemPrereq[];
  conceptPrereqs: ConceptPrereq[];
  allSatisfied: boolean;
}

export function getPrerequisiteStatus(
  problem: Problem,
  completedSlugs: string[],
  allProblems: Problem[]
): PrerequisiteStatus {
  const completed = new Set(completedSlugs);
  const problemMap = new Map(allProblems.map((p) => [p.slug, p]));

  const problemPrereqs: ProblemPrereq[] = (problem.prerequisites?.problems ?? []).map((slug) => {
    const p = problemMap.get(slug);
    return {
      slug,
      title: p?.title ?? slug,
      completed: completed.has(slug),
    };
  });

  const conceptPrereqs: ConceptPrereq[] = (problem.prerequisites?.concepts ?? []).map((conceptId) => {
    const concept: ConceptInfo | undefined = conceptMap.get(conceptId);
    // A concept is satisfied if its learnPath points to a problem slug that's completed,
    // or if it's a tutorial link (starts with /) - we consider those always satisfied as
    // tutorials are freely available
    let satisfied = false;
    if (concept) {
      if (concept.learnPath.startsWith('/')) {
        // Tutorial link - always accessible
        satisfied = true;
      } else {
        // It's a problem slug
        satisfied = completed.has(concept.learnPath);
      }
    }
    return {
      id: conceptId,
      displayName: concept?.displayName ?? conceptId,
      description: concept?.description ?? '',
      satisfied,
      learnPath: concept?.learnPath ?? '#',
    };
  });

  const allSatisfied =
    problemPrereqs.every((p) => p.completed) &&
    conceptPrereqs.every((c) => c.satisfied);

  return { problemPrereqs, conceptPrereqs, allSatisfied };
}

export function getUnsatisfiedCount(status: PrerequisiteStatus): number {
  const unsatisfiedProblems = status.problemPrereqs.filter((p) => !p.completed).length;
  const unsatisfiedConcepts = status.conceptPrereqs.filter((c) => !c.satisfied).length;
  return unsatisfiedProblems + unsatisfiedConcepts;
}
