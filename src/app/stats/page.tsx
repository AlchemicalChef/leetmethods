import { getProblemSummaries } from '@/lib/problems/loader';
import { StatsOverview } from '@/components/stats/StatsOverview';
import type { Metadata } from 'next';

export const metadata: Metadata = {
  title: 'Your Stats - LeetMethods',
  description: 'Track your progress across all Coq proof problems',
};

export default async function StatsPage() {
  const problems = await getProblemSummaries();

  return (
    <div className="max-w-4xl mx-auto px-4 py-12">
      <h1 className="text-4xl font-bold mb-2">Your Stats</h1>
      <p className="text-muted-foreground mb-8">Track your progress across all problems</p>
      <StatsOverview problems={problems} />
    </div>
  );
}
