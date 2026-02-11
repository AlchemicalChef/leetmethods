/**
 * @module LearnHub
 *
 * Top-level container component for the Learn page (`/learn`).
 *
 * This component orchestrates the entire learning experience by composing
 * together several sub-components in a logical layout:
 *   1. ProgressOverview -- aggregate problem-solving stats shown at the top
 *   2. LearningPathsSection -- guided path cards for structured learning
 *   3. Tabbed content area -- Concepts, Tactic Reference, and Playground
 *
 * The tab system uses Radix UI Tabs (via shadcn/ui) to let users switch
 * between conceptual guides, a searchable tactic encyclopedia, and an
 * interactive Coq code playground without navigating away from the page.
 *
 * Design decision: The ProgressOverview is conditionally rendered only when
 * there are problems available. This avoids showing an empty/zero progress
 * bar on first load or if the problem loader returns nothing.
 *
 * This is a client component because child components rely on Zustand stores
 * (localStorage-backed) and interactive state (tabs, search, code editing).
 */
'use client';

import { Tabs, TabsContent, TabsList, TabsTrigger } from '@/components/ui/tabs';
import { TacticReference } from './TacticReference';
import { TacticPlayground } from './TacticPlayground';
import { ConceptGuide } from './ConceptGuide';
import { ProgressOverview } from './ProgressOverview';
import { LearningPathsSection } from './LearningPathsSection';
import type { ProblemSummary } from '@/lib/problems/types';

/**
 * Props for the LearnHub component.
 *
 * @property problems - Array of all available problem summaries, used by
 *   ProgressOverview to compute completion percentages per category.
 *   This is passed down from the page-level server component which loads
 *   problems synchronously via `getProblemSummaries()`.
 */
interface LearnHubProps {
  problems: ProblemSummary[];
}

/**
 * Renders the full Learn page layout with progress tracking, learning paths,
 * and tabbed reference/playground content.
 *
 * @param props - Component props containing the list of all problems.
 * @returns The complete Learn page UI.
 */
export function LearnHub({ problems }: LearnHubProps) {

  return (
    <div className="space-y-8">
      {/* Progress overview -- only rendered when problems exist to avoid empty state */}
      {problems.length > 0 && <ProgressOverview problems={problems} />}

      {/* Learning paths section -- displays guided path cards in a responsive grid */}
      <LearningPathsSection />

      {/* Tabbed content area for reference material and interactive tools.
          Defaults to "concepts" tab as it provides the most foundational content
          for new users discovering the Learn page. */}
      <Tabs defaultValue="concepts" className="w-full">
        {/* Tab triggers are left-aligned (justify-start) to follow conventional
            tab bar UX rather than stretching across the full width */}
        <TabsList className="w-full justify-start">
          <TabsTrigger value="concepts">Concepts</TabsTrigger>
          <TabsTrigger value="tactics">Tactic Reference</TabsTrigger>
          <TabsTrigger value="playground">Playground</TabsTrigger>
        </TabsList>

        {/* Concept guide -- expandable accordion of core Coq concepts with examples */}
        <TabsContent value="concepts" className="mt-6">
          <ConceptGuide />
        </TabsContent>

        {/* Tactic reference -- searchable, filterable encyclopedia of Coq tactics */}
        <TabsContent value="tactics" className="mt-6">
          <TacticReference />
        </TabsContent>

        {/* Playground -- interactive code editor for experimenting with Coq tactics */}
        <TabsContent value="playground" className="mt-6">
          <TacticPlayground />
        </TabsContent>
      </Tabs>
    </div>
  );
}
