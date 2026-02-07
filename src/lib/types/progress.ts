import type { SrsData } from '@/lib/srs';

export interface ProblemProgress {
  slug: string;
  completed: boolean;
  completedAt: number | null;
  attempts: number;
  hintsUsed: number;
  solveStartedAt: number | null;
  solveDurationMs: number | null;
  srs: SrsData | null;
  reviewAttempts: number;
  reviewHintsUsed: number;
  isReviewing: boolean;
}

export interface StreakData {
  currentStreak: number;
  longestStreak: number;
  lastSolveDate: string | null; // ISO date string YYYY-MM-DD
}

export interface DueReviewInfo {
  slug: string;
  overdueDays: number;
}
