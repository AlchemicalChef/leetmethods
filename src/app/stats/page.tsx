/**
 * @module StatsPage
 *
 * Server-rendered page for the `/stats` route -- the user statistics dashboard.
 *
 * This page displays the user's overall progress across all built-in Coq
 * proof problems, including metrics such as completion counts, category
 * breakdowns, streak information, and SRS (Spaced Repetition System)
 * review schedules.
 *
 * Architecture notes:
 * - This is a **server component** that loads problem summaries synchronously
 *   via `getProblemSummaries()`. The summaries provide the total problem
 *   count and category information needed to calculate completion percentages.
 * - The `StatsOverview` client component combines server-provided problem
 *   data with client-side progress from the Zustand `progressStore`
 *   (persisted in localStorage) to compute and display statistics.
 * - Because all user data lives in localStorage (no backend), stats are
 *   computed entirely on the client. The server only provides the reference
 *   data (the full problem list) that the client needs to calculate
 *   percentages and identify unsolved problems.
 */

import { getProblemSummaries } from '@/lib/problems/loader';
import { StatsOverview } from '@/components/stats/StatsOverview';
import type { Metadata } from 'next';

/**
 * Static page metadata for the stats dashboard.
 * Sets a descriptive title and description for SEO and the browser tab.
 */
export const metadata: Metadata = {
  title: 'Your Stats - LeetMethods',
  description: 'Track your progress across all Coq proof problems',
};

/**
 * Stats dashboard page component.
 *
 * Loads all problem summaries on the server and delegates rendering to
 * the interactive `StatsOverview` client component, which merges the
 * problem list with the user's localStorage-persisted progress data.
 *
 * @returns The stats page with heading, subheading, and the StatsOverview
 *   component.
 */
export default function StatsPage() {
  const problems = getProblemSummaries();

  return (
    <div className="max-w-4xl mx-auto px-4 py-12">
      <h1 className="text-4xl font-bold mb-2">Your Stats</h1>
      <p className="text-muted-foreground mb-8">Track your progress across all problems</p>
      <StatsOverview problems={problems} />
    </div>
  );
}
