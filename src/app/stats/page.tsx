'use client';

import { useEffect, useState } from 'react';
import { StatsOverview } from '@/components/stats/StatsOverview';
import type { ProblemSummary } from '@/lib/problems/types';

export default function StatsPage() {
  const [problems, setProblems] = useState<ProblemSummary[]>([]);
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    fetch('/api/problems')
      .then((res) => res.json())
      .then((data) => {
        setProblems(data);
        setLoading(false);
      })
      .catch(() => setLoading(false));
  }, []);

  return (
    <div className="max-w-4xl mx-auto px-4 py-12">
      <h1 className="text-4xl font-bold mb-2">Your Stats</h1>
      <p className="text-muted-foreground mb-8">Track your progress across all problems</p>

      {loading ? (
        <div className="text-center py-12 text-muted-foreground">Loading stats...</div>
      ) : (
        <StatsOverview problems={problems} />
      )}
    </div>
  );
}
