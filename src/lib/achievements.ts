import type { ProblemProgress, StreakData } from '@/lib/types/progress';
import type { ProblemSummary, Category } from '@/lib/problems/types';

export interface Achievement {
  id: string;
  title: string;
  description: string;
  icon: string; // emoji
  category: 'milestone' | 'mastery' | 'skill' | 'dedication';
}

export const achievements: Achievement[] = [
  // Milestones
  { id: 'first-proof', title: 'First Proof', description: 'Complete your first proof', icon: '🎯', category: 'milestone' },
  { id: 'five-proofs', title: 'Getting Started', description: 'Complete 5 proofs', icon: '🌱', category: 'milestone' },
  { id: 'ten-proofs', title: 'Double Digits', description: 'Complete 10 proofs', icon: '🔟', category: 'milestone' },
  { id: 'all-proofs', title: 'Completionist', description: 'Complete all problems', icon: '🏆', category: 'milestone' },

  // Category mastery
  { id: 'logic-master', title: 'Logic Master', description: 'Complete all Logic problems', icon: '🧠', category: 'mastery' },
  { id: 'induction-master', title: 'Induction Expert', description: 'Complete all Induction problems', icon: '🔄', category: 'mastery' },
  { id: 'list-master', title: 'List Wrangler', description: 'Complete all List problems', icon: '📋', category: 'mastery' },
  { id: 'data-structures-master', title: 'Tree Climber', description: 'Complete all Data Structures problems', icon: '🌳', category: 'mastery' },
  { id: 'arithmetic-master', title: 'Number Cruncher', description: 'Complete all Arithmetic problems', icon: '🔢', category: 'mastery' },
  { id: 'relations-master', title: 'Relation Builder', description: 'Complete all Relations problems', icon: '🔗', category: 'mastery' },

  // Skill
  { id: 'no-hints', title: 'No Hints Needed', description: 'Complete a problem without using any hints', icon: '💡', category: 'skill' },
  { id: 'first-try', title: 'First Try', description: 'Complete a problem on the first attempt', icon: '⚡', category: 'skill' },
  { id: 'persistence', title: 'Persistence', description: 'Complete a problem after 10+ attempts', icon: '💪', category: 'skill' },

  // Dedication
  { id: 'streak-3', title: 'Hat Trick', description: 'Maintain a 3-day solve streak', icon: '🔥', category: 'dedication' },
  { id: 'first-review', title: 'First Review', description: 'Complete your first spaced review', icon: '🔄', category: 'dedication' },
  { id: 'ten-reviews', title: 'Review Master', description: 'Complete 10 spaced reviews', icon: '📚', category: 'dedication' },
  { id: 'perfect-recall', title: 'Perfect Recall', description: 'Complete a review on the first attempt with no hints', icon: '🧠', category: 'skill' },
];

const categoryMap: Record<string, Category> = {
  'logic-master': 'logic',
  'induction-master': 'induction',
  'list-master': 'lists',
  'arithmetic-master': 'arithmetic',
  'data-structures-master': 'data-structures',
  'relations-master': 'relations',
};

export function checkAchievements(
  progress: Record<string, ProblemProgress>,
  problems: ProblemSummary[],
  streakData: StreakData,
  unlockedIds: Set<string>
): string[] {
  const newlyUnlocked: string[] = [];
  const completed = Object.values(progress).filter((p) => p.completed);
  const completedCount = completed.length;

  const check = (id: string, condition: boolean) => {
    if (!unlockedIds.has(id) && condition) {
      newlyUnlocked.push(id);
    }
  };

  // Milestones
  check('first-proof', completedCount >= 1);
  check('five-proofs', completedCount >= 5);
  check('ten-proofs', completedCount >= 10);
  check('all-proofs', completedCount >= problems.length && problems.length > 0);

  // Category mastery
  for (const [achId, category] of Object.entries(categoryMap)) {
    const categoryProblems = problems.filter((p) => p.category === category);
    if (categoryProblems.length > 0) {
      const allCompleted = categoryProblems.every((p) => progress[p.slug]?.completed);
      check(achId, allCompleted);
    }
  }

  // Skill
  check('no-hints', completed.some((p) => p.hintsUsed === 0));
  check('first-try', completed.some((p) => p.attempts <= 1));
  check('persistence', completed.some((p) => p.attempts >= 10));

  // Dedication
  check('streak-3', streakData.longestStreak >= 3 || streakData.currentStreak >= 3);

  // SRS achievements
  const allProgress = Object.values(progress);
  let totalReviewCount = 0;
  let hasPerfectRecall = false;
  for (const p of allProgress) {
    if (p.srs) {
      totalReviewCount += p.srs.reviewCount;
      if (p.srs.reviewCount > 0 && p.srs.lastReviewQuality >= 5) {
        hasPerfectRecall = true;
      }
    }
  }
  check('first-review', totalReviewCount >= 1);
  check('ten-reviews', totalReviewCount >= 10);
  check('perfect-recall', hasPerfectRecall);

  return newlyUnlocked;
}
