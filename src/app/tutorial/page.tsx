/**
 * @module TutorialIndex
 *
 * Client-rendered page for the `/tutorial` route -- the tutorial hub.
 *
 * This page serves as the entry point for all interactive Coq tutorials.
 * Tutorials are organized into three "volume groups" that mirror the
 * Software Foundations curriculum:
 *
 *   1. **Logical Foundations (LF)** -- Core Coq skills: tactics, induction,
 *      data structures, and proof techniques.
 *   2. **Programming Language Foundations (PLF)** -- Formal semantics:
 *      defining languages, type systems, and verified interpreters.
 *   3. **Verified Functional Algorithms (VFA)** -- Verified implementations:
 *      sorting algorithms and data structures with proofs.
 *
 * Design decisions:
 *
 * - **Client component**: Marked 'use client' because the tutorial registry
 *   data is imported and iterated at render time, and the page uses
 *   interactive hover effects on tutorial cards. While the data itself is
 *   static, the component organization with dynamic icon rendering
 *   (`<group.icon>`) requires client-side React.
 *
 * - **Volume groups are hardcoded**: The `volumeGroups` array defines
 *   which tutorials belong to which volume and in what order. This is
 *   intentional -- the curriculum structure is a pedagogical decision,
 *   not something derived from the tutorial registry data.
 *
 * - **Ungrouped tutorials fallback**: An IIFE at the bottom of the render
 *   tree detects any tutorials in the registry that are NOT listed in any
 *   volume group and renders them in an "Other Tutorials" section. This
 *   ensures newly added tutorials are always visible even if they have
 *   not yet been assigned to a volume group.
 *
 * - **Title cleanup**: Tutorial titles in the registry are prefixed with
 *   "Tutorial: " (e.g., "Tutorial: Basics"). The display strips this prefix
 *   via `.replace('Tutorial: ', '')` since the page heading already
 *   establishes the tutorial context.
 */
'use client';

import Link from 'next/link';
import { GraduationCap, ArrowRight, BookOpen, FlaskConical, Database } from 'lucide-react';
import { tutorials } from '@/lib/tutorial/registry';

/* ------------------------------------------------------------------ */
/*  Volume group definitions                                           */
/* ------------------------------------------------------------------ */

/**
 * Defines the three volume groups that organize tutorials into a
 * structured curriculum. Each group has:
 *   - `title`: Display name including the Software Foundations abbreviation
 *   - `icon`: Lucide icon component rendered next to the section heading
 *   - `description`: One-sentence summary of what the volume covers
 *   - `slugs`: Ordered array of tutorial slugs belonging to this volume;
 *     order determines display order and implies pedagogical sequence
 */
const volumeGroups = [
  {
    title: 'Logical Foundations (LF)',
    icon: BookOpen,
    description: 'Core Coq skills: tactics, induction, data structures, and proof techniques.',
    slugs: ['basics', 'applied-methods', 'logic-negation', 'proof-strategies', 'polymorphism', 'inductive-props'],
  },
  {
    title: 'Programming Language Foundations (PLF)',
    icon: FlaskConical,
    description: 'Formal semantics: defining languages, type systems, and verified interpreters.',
    slugs: ['defining-languages', 'type-systems'],
  },
  {
    title: 'Verified Functional Algorithms (VFA)',
    icon: Database,
    description: 'Verified implementations: sorting algorithms and data structures with proofs.',
    slugs: ['verified-sorting', 'verified-data-structures'],
  },
];

/* ------------------------------------------------------------------ */
/*  Page component                                                     */
/* ------------------------------------------------------------------ */

/**
 * Tutorial index page component.
 *
 * Renders the tutorial hub with volume-grouped sections and an optional
 * "Other Tutorials" section for any tutorials not assigned to a group.
 *
 * @returns The tutorial index page with grouped tutorial links.
 */
export default function TutorialIndex() {
  return (
    <main className="max-w-4xl mx-auto px-4 py-8">
      {/* Page header */}
      <div className="mb-8">
        <h1 className="text-3xl font-bold flex items-center gap-3 mb-2">
          <GraduationCap className="h-8 w-8 text-primary" />
          Tutorials
        </h1>
        <p className="text-muted-foreground">
          Learn Coq proof techniques progressively, based on the Software Foundations curriculum.
          Each tutorial builds on the previous one.
        </p>
      </div>

      <div className="space-y-8">
        {/* Render each volume group as a section with its tutorials */}
        {volumeGroups.map((group) => (
          <section key={group.title}>
            <div className="flex items-center gap-2 mb-3">
              <group.icon className="h-5 w-5 text-primary" />
              <h2 className="text-xl font-semibold">{group.title}</h2>
            </div>
            <p className="text-sm text-muted-foreground mb-4">{group.description}</p>
            <div className="grid gap-3">
              {group.slugs.map((slug) => {
                const tutorial = tutorials.find((t) => t.slug === slug);
                /**
                 * Skip rendering if a slug in the volume group does not
                 * match any registered tutorial. This guards against stale
                 * references if a tutorial is removed from the registry
                 * but the volume group definition is not updated.
                 */
                if (!tutorial) return null;
                return (
                  <Link
                    key={slug}
                    href={`/tutorial/${slug}`}
                    className="group flex items-center justify-between p-4 rounded-lg border bg-card hover:bg-accent/50 transition-colors"
                  >
                    <div>
                      <h3 className="font-medium group-hover:text-primary transition-colors">
                        {tutorial.title.replace('Tutorial: ', '')}
                      </h3>
                      <p className="text-sm text-muted-foreground">
                        {tutorial.steps.length} steps
                      </p>
                    </div>
                    <ArrowRight className="h-4 w-4 text-muted-foreground group-hover:text-primary transition-colors" />
                  </Link>
                );
              })}
            </div>
          </section>
        ))}

        {/*
         * Catch-all section for tutorials that exist in the registry but
         * are not assigned to any volume group. This prevents tutorials from
         * being silently invisible if they are added to the registry without
         * updating the volumeGroups array above.
         */}
        {(() => {
          const groupedSlugs = new Set(volumeGroups.flatMap((g) => g.slugs));
          const ungrouped = tutorials.filter((t) => !groupedSlugs.has(t.slug));
          if (ungrouped.length === 0) return null;
          return (
            <section>
              <h2 className="text-xl font-semibold mb-3">Other Tutorials</h2>
              <div className="grid gap-3">
                {ungrouped.map((tutorial) => (
                  <Link
                    key={tutorial.slug}
                    href={`/tutorial/${tutorial.slug}`}
                    className="group flex items-center justify-between p-4 rounded-lg border bg-card hover:bg-accent/50 transition-colors"
                  >
                    <div>
                      <h3 className="font-medium group-hover:text-primary transition-colors">
                        {tutorial.title.replace('Tutorial: ', '')}
                      </h3>
                      <p className="text-sm text-muted-foreground">
                        {tutorial.steps.length} steps
                      </p>
                    </div>
                    <ArrowRight className="h-4 w-4 text-muted-foreground group-hover:text-primary transition-colors" />
                  </Link>
                ))}
              </div>
            </section>
          );
        })()}
      </div>
    </main>
  );
}
