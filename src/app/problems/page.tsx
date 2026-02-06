import { getProblemSummaries } from '@/lib/problems/loader';
import { ProblemListWithProgress } from '@/components/problem/ProblemListWithProgress';
import type { Metadata } from 'next';

export const metadata: Metadata = {
  title: 'Problems - LeetMethods',
  description: 'Browse and solve Coq proof problems organized by difficulty and category',
};

export default async function ProblemsPage() {
  const problems = await getProblemSummaries();

  return (
    <div className="max-w-4xl mx-auto px-4 py-8">
      <h1 className="text-3xl font-bold mb-6">Problems</h1>
      <ProblemListWithProgress problems={problems} />
    </div>
  );
}
