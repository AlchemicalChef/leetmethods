'use client';

import { useEffect, useState } from 'react';
import { Tabs, TabsContent, TabsList, TabsTrigger } from '@/components/ui/tabs';
import { TacticReference } from './TacticReference';
import { TacticPlayground } from './TacticPlayground';
import { ConceptGuide } from './ConceptGuide';
import { ProgressOverview } from './ProgressOverview';
import { LearningPathsSection } from './LearningPathsSection';
import type { ProblemSummary } from '@/lib/problems/types';

export function LearnHub() {
  const [problems, setProblems] = useState<ProblemSummary[]>([]);

  useEffect(() => {
    fetch('/api/problems')
      .then((res) => res.json())
      .then(setProblems)
      .catch(() => {});
  }, []);

  return (
    <div className="space-y-8">
      {/* Progress overview */}
      {problems.length > 0 && <ProgressOverview problems={problems} />}

      {/* Learning Paths */}
      <LearningPathsSection />

      {/* Tabs */}
      <Tabs defaultValue="concepts" className="w-full">
        <TabsList className="w-full justify-start">
          <TabsTrigger value="concepts">Concepts</TabsTrigger>
          <TabsTrigger value="tactics">Tactic Reference</TabsTrigger>
          <TabsTrigger value="playground">Playground</TabsTrigger>
        </TabsList>

        <TabsContent value="concepts" className="mt-6">
          <ConceptGuide />
        </TabsContent>

        <TabsContent value="tactics" className="mt-6">
          <TacticReference />
        </TabsContent>

        <TabsContent value="playground" className="mt-6">
          <TacticPlayground />
        </TabsContent>
      </Tabs>
    </div>
  );
}
