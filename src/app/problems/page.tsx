'use client';

import { useEffect, useState } from 'react';
import { ProblemList } from '@/components/problem';
import { useProgressStore } from '@/store/progressStore';
import type { ProblemSummary } from '@/lib/problems/types';

export default function ProblemsPage() {
  const [problems, setProblems] = useState<ProblemSummary[]>([]);
  const [loading, setLoading] = useState(true);
  const { getCompletedSlugs } = useProgressStore();

  useEffect(() => {
    async function loadProblems() {
      try {
        const res = await fetch('/api/problems');
        const data = await res.json();
        setProblems(data);
      } catch (error) {
        console.error('Failed to load problems:', error);
      } finally {
        setLoading(false);
      }
    }

    loadProblems();
  }, []);

  if (loading) {
    return (
      <div className="max-w-4xl mx-auto px-4 py-8">
        <div className="animate-pulse">
          <div className="h-8 bg-muted rounded w-48 mb-6" />
          <div className="space-y-3">
            {[1, 2, 3, 4, 5].map((i) => (
              <div key={i} className="h-20 bg-muted rounded" />
            ))}
          </div>
        </div>
      </div>
    );
  }

  return (
    <div className="max-w-4xl mx-auto px-4 py-8">
      <h1 className="text-3xl font-bold mb-6">Problems</h1>
      <ProblemList problems={problems} completedSlugs={getCompletedSlugs()} />
    </div>
  );
}
