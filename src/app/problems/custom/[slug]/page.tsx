'use client';

import { useEffect, useState } from 'react';
import { useParams, useRouter } from 'next/navigation';
import { useCustomProblemStore } from '@/store/customProblemStore';
import { ProblemSolver } from '@/components/problem/ProblemSolver';
import { getAllProblemsSync } from '@/lib/problems/loader';
import type { ProblemSummary } from '@/lib/problems/types';

export default function CustomProblemPage() {
  const params = useParams();
  const router = useRouter();
  const slug = params.slug as string;
  const getProblem = useCustomProblemStore((s) => s.getProblem);
  const [hydrated, setHydrated] = useState(false);

  useEffect(() => {
    setHydrated(true);
  }, []);

  if (!hydrated) {
    return (
      <div className="flex items-center justify-center h-[calc(100vh-64px)]">
        <div className="animate-spin rounded-full h-8 w-8 border-2 border-primary border-t-transparent" />
      </div>
    );
  }

  const problem = getProblem(slug);

  if (!problem) {
    return (
      <div className="max-w-4xl mx-auto px-4 py-16 text-center">
        <h1 className="text-2xl font-bold mb-4">Custom Problem Not Found</h1>
        <p className="text-muted-foreground mb-6">
          This custom problem may have been deleted or the URL is incorrect.
        </p>
        <button onClick={() => router.push('/problems')} className="text-primary hover:underline">
          Back to Problems
        </button>
      </div>
    );
  }

  const builtinSummaries: ProblemSummary[] = getAllProblemsSync().map(
    ({ id, slug, title, difficulty, category, tags }) => ({ id, slug, title, difficulty, category, tags })
  );

  return <ProblemSolver problem={problem} allProblems={builtinSummaries} />;
}
