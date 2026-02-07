import type { Metadata } from 'next';
import { LearnHub } from '@/components/learn/LearnHub';
import { getAllProblemsSync } from '@/lib/problems/loader';

export const metadata: Metadata = {
  title: 'Learn Coq | LeetMethods',
  description: 'A gentle introduction to theorem proving with Coq. Follow guided learning paths from beginner to advanced.',
};

export default function LearnPage() {
  const problems = getAllProblemsSync();

  return (
    <div className="max-w-4xl mx-auto px-4 py-12">
      <h1 className="text-4xl font-bold mb-4">Learn Coq</h1>
      <p className="text-xl text-muted-foreground mb-8">
        A gentle introduction to theorem proving with Coq
      </p>
      <LearnHub problems={problems} />
    </div>
  );
}
