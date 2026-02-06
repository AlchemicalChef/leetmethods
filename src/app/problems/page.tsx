'use client';

import { useEffect, useState, useCallback } from 'react';
import { ProblemList } from '@/components/problem';
import { useProgressStore } from '@/store/progressStore';
import type { ProblemSummary } from '@/lib/problems/types';

export default function ProblemsPage() {
  const [problems, setProblems] = useState<ProblemSummary[]>([]);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const { getCompletedSlugs } = useProgressStore();

  const loadProblems = useCallback(async () => {
    setLoading(true);
    setError(null);
    try {
      const res = await fetch('/api/problems');
      if (!res.ok) {
        throw new Error(`Failed to load problems (${res.status})`);
      }
      const data = await res.json();
      setProblems(data);
    } catch (err) {
      console.error('Failed to load problems:', err);
      setError(err instanceof Error ? err.message : 'Failed to load problems');
    } finally {
      setLoading(false);
    }
  }, []);

  useEffect(() => {
    loadProblems();
  }, [loadProblems]);

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

  if (error) {
    return (
      <div className="max-w-4xl mx-auto px-4 py-8">
        <h1 className="text-3xl font-bold mb-6">Problems</h1>
        <div className="rounded-md border border-red-200 dark:border-red-900 bg-red-50 dark:bg-red-950/30 p-4">
          <p className="text-red-700 dark:text-red-400 text-sm">{error}</p>
          <button
            onClick={loadProblems}
            className="mt-3 px-4 py-2 text-sm font-medium rounded-md bg-red-100 dark:bg-red-900/50 text-red-700 dark:text-red-400 hover:bg-red-200 dark:hover:bg-red-900/70 transition-colors"
          >
            Retry
          </button>
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
