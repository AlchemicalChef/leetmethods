/**
 * @module HomePage
 *
 * Landing page for LeetMethods -- the main entry point users see at `/`.
 *
 * This is a **server component** (no 'use client' directive), which means it can
 * call synchronous data loaders like `getAllProblems()` at module scope. The
 * problem data is used at build time to compute per-category counts and to
 * determine a sensible default "first problem" link for the call-to-action button.
 *
 * The page is structured as a classic marketing-style landing page with four
 * sections:
 *   1. Hero -- headline, tagline, and primary CTA buttons
 *   2. Features -- four cards explaining key platform benefits
 *   3. Categories -- one card per problem category with problem counts
 *   4. CTA -- a final nudge linking to the first easy problem
 *
 * Design decisions:
 * - Category counts are computed once at module scope (they never change at
 *   runtime since problems are statically defined).
 * - The "first problem" slug falls back through: first easy problem -> first
 *   problem of any difficulty -> hardcoded 'modus-ponens' slug. This ensures
 *   the CTA link is always valid even if the problem set changes.
 * - `FeatureCard` and `CategoryCard` are private helper components co-located
 *   here because they are only used on the landing page.
 */

import Link from 'next/link';
import { Button } from '@/components/ui/button';
import { Card } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import { ArrowRight, BookOpen, Code, Trophy, Zap } from 'lucide-react';
import { getAllProblems } from '@/lib/problems/loader';

/* ------------------------------------------------------------------ */
/*  Static data computed at module scope (build time / server render)  */
/* ------------------------------------------------------------------ */

/**
 * Full list of built-in problems, loaded synchronously from the static
 * JSON-based problem registry. Used to derive category counts and the
 * first-problem slug below.
 */
const allProblems = getAllProblems();

/**
 * A mapping from category name to the number of problems in that category.
 * Computed once via an IIFE so the landing page can display counts without
 * re-iterating over the problem list on every render.
 */
const categoryCounts = (() => {
  const counts: Record<string, number> = {};
  for (const p of allProblems) counts[p.category] = (counts[p.category] ?? 0) + 1;
  return counts;
})();

/**
 * Determines the slug for the "Try Your First Problem" CTA button.
 * Preference order:
 *   1. The first problem whose difficulty is 'easy'
 *   2. The first problem regardless of difficulty
 *   3. A hardcoded fallback ('modus-ponens') so the link is never broken
 */
const firstProblemSlug = allProblems.find((p) => p.difficulty === 'easy')?.slug ?? allProblems[0]?.slug ?? 'modus-ponens';

/* ------------------------------------------------------------------ */
/*  Page component                                                     */
/* ------------------------------------------------------------------ */

/**
 * Root landing page component rendered at `/`.
 *
 * This is a Next.js App Router server component. It renders static HTML with
 * no client-side JavaScript hydration required, keeping the initial page load
 * fast.
 *
 * @returns The full landing page JSX tree.
 */
export default function Home() {
  return (
    <div className="min-h-screen">
      {/* Hero section -- primary headline and navigation CTAs */}
      <section className="py-20 px-4">
        <div className="max-w-4xl mx-auto text-center">
          <Badge variant="secondary" className="mb-4">
            Learn Formal Verification
          </Badge>
          <h1 className="text-5xl font-bold mb-6">
            Master Coq Proofs
            <span className="text-primary block mt-2">One Theorem at a Time</span>
          </h1>
          <p className="text-xl text-muted-foreground mb-8 max-w-2xl mx-auto">
            LeetMethods is an interactive platform for practicing formal proofs in Coq.
            Solve challenges, build your skills, and prove theorems directly in your browser.
          </p>
          <div className="flex gap-4 justify-center">
            <Link href="/tutorial">
              <Button size="lg" className="gap-2">
                Start Tutorial
                <ArrowRight className="h-4 w-4" />
              </Button>
            </Link>
            <Link href="/problems">
              <Button size="lg" variant="outline">
                Browse Problems
              </Button>
            </Link>
          </div>
        </div>
      </section>

      {/* Features section -- four benefit cards in a responsive grid */}
      <section className="py-16 px-4 bg-muted/30">
        <div className="max-w-6xl mx-auto">
          <h2 className="text-3xl font-bold text-center mb-12">Why LeetMethods?</h2>
          <div className="grid md:grid-cols-2 lg:grid-cols-4 gap-6">
            <FeatureCard
              icon={<Code className="h-8 w-8" />}
              title="Browser-Based"
              description="No installation needed. Write and verify Coq proofs directly in your browser with jsCoq."
            />
            <FeatureCard
              icon={<Zap className="h-8 w-8" />}
              title="Instant Feedback"
              description="See your proof goals update in real-time as you apply tactics."
            />
            <FeatureCard
              icon={<BookOpen className="h-8 w-8" />}
              title="Curated Problems"
              description="Problems organized by difficulty and category, from basic logic to advanced induction."
            />
            <FeatureCard
              icon={<Trophy className="h-8 w-8" />}
              title="Track Progress"
              description="Your solutions are saved locally. Watch your completion rate grow."
            />
          </div>
        </div>
      </section>

      {/* Categories section -- one card per problem category linking to filtered view */}
      <section className="py-16 px-4">
        <div className="max-w-4xl mx-auto">
          <h2 className="text-3xl font-bold text-center mb-12">Problem Categories</h2>
          <div className="grid sm:grid-cols-2 lg:grid-cols-3 gap-4">
            <CategoryCard
              title="Logic"
              description="Propositional and predicate logic proofs"
              count={categoryCounts['logic'] ?? 0}
            />
            <CategoryCard
              title="Booleans"
              description="Boolean algebra and decidable properties"
              count={categoryCounts['booleans'] ?? 0}
            />
            <CategoryCard
              title="Induction"
              description="Mathematical and structural induction"
              count={categoryCounts['induction'] ?? 0}
            />
            <CategoryCard
              title="Lists"
              description="Proofs about list operations"
              count={categoryCounts['lists'] ?? 0}
            />
            <CategoryCard
              title="Arithmetic"
              description="Number theory and arithmetic proofs"
              count={categoryCounts['arithmetic'] ?? 0}
            />
            <CategoryCard
              title="Data Structures"
              slug="data-structures"
              description="Trees, BSTs, and recursive data types"
              count={categoryCounts['data-structures'] ?? 0}
            />
            <CategoryCard
              title="Relations"
              description="Ordering, equality, and relational proofs"
              count={categoryCounts['relations'] ?? 0}
            />
          </div>
        </div>
      </section>

      {/* Final CTA section -- links directly to the first easy problem */}
      <section className="py-20 px-4 bg-primary/5">
        <div className="max-w-2xl mx-auto text-center">
          <h2 className="text-3xl font-bold mb-4">Ready to Start?</h2>
          <p className="text-muted-foreground mb-8">
            Jump into your first proof. No signup required.
          </p>
          <Link href={`/problems/${firstProblemSlug}`}>
            <Button size="lg" className="gap-2">
              Try Your First Problem
              <ArrowRight className="h-4 w-4" />
            </Button>
          </Link>
        </div>
      </section>

      {/* Footer -- minimal branding and attribution */}
      <footer className="py-8 px-4 border-t">
        <div className="max-w-4xl mx-auto text-center text-sm text-muted-foreground">
          <p>Built with Next.js, CodeMirror, and jsCoq</p>
          <p className="mt-2">
            Inspired by{' '}
            <a
              href="https://softwarefoundations.cis.upenn.edu/"
              target="_blank"
              rel="noopener noreferrer"
              className="underline hover:text-foreground"
            >
              Software Foundations
            </a>
          </p>
        </div>
      </footer>
    </div>
  );
}

/* ------------------------------------------------------------------ */
/*  Private helper components                                          */
/* ------------------------------------------------------------------ */

/**
 * A card displaying a single platform feature (icon, title, description).
 * Used exclusively in the "Why LeetMethods?" section of the landing page.
 *
 * @param props.icon - A React node (typically a Lucide icon) rendered inside
 *   a circular accent-colored container.
 * @param props.title - Short feature name displayed as the card heading.
 * @param props.description - One-sentence explanation of the feature.
 * @returns A centered card element with icon, title, and description.
 */
function FeatureCard({
  icon,
  title,
  description,
}: {
  icon: React.ReactNode;
  title: string;
  description: string;
}) {
  return (
    <Card className="p-6 text-center">
      <div className="inline-flex items-center justify-center w-16 h-16 rounded-full bg-primary/10 text-primary mb-4">
        {icon}
      </div>
      <h3 className="font-semibold mb-2">{title}</h3>
      <p className="text-sm text-muted-foreground">{description}</p>
    </Card>
  );
}

/**
 * A clickable card representing a problem category. Links to the problems
 * page pre-filtered by that category via a query parameter.
 *
 * @param props.title - Display name of the category (e.g. "Logic").
 * @param props.description - Short description of what the category covers.
 * @param props.count - Number of problems in this category (shown as a badge).
 * @param props.slug - Optional URL slug override. When omitted, the slug is
 *   derived by lowercasing the title. This is needed for categories like
 *   "Data Structures" whose slug is "data-structures" (hyphenated), which
 *   cannot be derived from `title.toLowerCase()` alone.
 * @returns A link-wrapped card element.
 */
function CategoryCard({
  title,
  description,
  count,
  slug,
}: {
  title: string;
  description: string;
  count: number;
  slug?: string;
}) {
  return (
    <Link href={`/problems?category=${slug ?? title.toLowerCase()}`}>
      <Card className="p-4 hover:bg-muted/50 transition-colors cursor-pointer">
        <div className="flex justify-between items-start">
          <div>
            <h3 className="font-semibold">{title}</h3>
            <p className="text-sm text-muted-foreground mt-1">{description}</p>
          </div>
          <Badge variant="secondary">{count}</Badge>
        </div>
      </Card>
    </Link>
  );
}
