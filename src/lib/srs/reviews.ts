import type { SrsData } from './algorithm';
import { isReviewDue, daysOverdue } from './algorithm';

const DAILY_REVIEW_CAP = 5;

export interface DueReview {
  slug: string;
  srs: SrsData;
  overdueDays: number;
}

export interface ReviewStats {
  totalReviews: number;
  dueCount: number;
  dailyCapReached: boolean;
  averageEase: number;
}

export function getDueProblems(
  srsMap: Record<string, SrsData>,
  completedToday: number = 0
): DueReview[] {
  const due: DueReview[] = [];
  for (const [slug, srs] of Object.entries(srsMap)) {
    if (isReviewDue(srs)) {
      due.push({ slug, srs, overdueDays: daysOverdue(srs) });
    }
  }
  // Sort by urgency (most overdue first)
  due.sort((a, b) => b.overdueDays - a.overdueDays);
  // Cap at daily limit minus already completed reviews today
  const remaining = Math.max(0, DAILY_REVIEW_CAP - completedToday);
  return due.slice(0, remaining);
}

export function getReviewStats(srsMap: Record<string, SrsData>): ReviewStats {
  const entries = Object.values(srsMap);
  const totalReviews = entries.reduce((sum, s) => sum + s.reviewCount, 0);
  const dueCount = entries.filter((s) => isReviewDue(s)).length;
  const averageEase = entries.length > 0
    ? entries.reduce((sum, s) => sum + s.easeFactor, 0) / entries.length
    : 2.5;

  return {
    totalReviews,
    dueCount,
    dailyCapReached: false, // caller can override based on completedToday
    averageEase,
  };
}
