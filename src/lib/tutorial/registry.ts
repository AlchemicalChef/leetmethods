/**
 * @module TutorialRegistry
 *
 * Central registry for all interactive tutorials in LeetMethods.
 *
 * This module is the single source of truth for tutorial metadata and
 * content. Every tutorial in the application must be registered here to
 * be accessible via the `/tutorial/[slug]` dynamic route.
 *
 * Architecture:
 * - Each tutorial is represented by a `TutorialConfig` object that bundles
 *   the tutorial's URL slug, display title, localStorage key for progress
 *   persistence, the array of `TutorialStep` definitions, and a link to
 *   the next tutorial in the curriculum sequence.
 * - Tutorial step definitions are authored in separate files (one per
 *   tutorial) and imported here. This keeps the registry file focused on
 *   configuration rather than content.
 * - The registry is organized to follow the Software Foundations curriculum:
 *   Logical Foundations -> Programming Language Foundations -> Verified
 *   Functional Algorithms. The `completionLink` on each entry chains
 *   tutorials together in this pedagogical sequence.
 *
 * Adding a new tutorial:
 *   1. Create a new steps file (e.g., `src/lib/tutorial/my-topic-steps.ts`)
 *      exporting a `TutorialStep[]` array.
 *   2. Import the steps array in this file.
 *   3. Add a new `TutorialConfig` entry to the `tutorials` array with a
 *      unique `slug` and `storageKey`.
 *   4. Update the `completionLink` of the preceding tutorial to point to
 *      the new one.
 *   5. Optionally add the slug to the `volumeGroups` in
 *      `src/app/tutorial/page.tsx` so it appears in the correct curriculum
 *      section (otherwise it will appear in the "Other Tutorials" fallback).
 *
 * Key constraints:
 * - `slug` values must be URL-safe (lowercase, hyphenated).
 * - `storageKey` values must be unique across all tutorials to avoid
 *   progress data collisions in localStorage.
 * - The `completionLink` of the last tutorial in the sequence should
 *   point outside the tutorial system (e.g., `/learn`).
 */

import type { TutorialStep } from './types';
import { tutorialSteps } from './tutorial-steps';
import { appliedMethodsSteps } from './applied-methods-steps';
import { logicNegationSteps } from './logic-negation-steps';
import { proofStrategiesSteps } from './proof-strategies-steps';
import { polymorphismSteps } from './polymorphism-steps';
import { inductivePropsSteps } from './inductive-props-steps';
import { definingLanguagesSteps } from './defining-languages-steps';
import { typeSystemsSteps } from './type-systems-steps';
import { verifiedSortingSteps } from './verified-sorting-steps';
import { verifiedDataStructuresSteps } from './verified-data-structures-steps';
import { securityNoninterferenceSteps } from './security-noninterference-steps';
import { securityIfcSteps } from './security-ifc-steps';
import { securityConstantTimeSteps } from './security-constant-time-steps';

/* ------------------------------------------------------------------ */
/*  Types                                                              */
/* ------------------------------------------------------------------ */

/**
 * Configuration object for a single tutorial.
 *
 * @property slug - URL-safe identifier used in the `/tutorial/[slug]` route.
 * @property title - Display title shown in the tutorial page header and
 *   the tutorial index. By convention, prefixed with "Tutorial: ".
 * @property storageKey - Unique key used to persist the user's progress
 *   (current step index) in localStorage. Must be globally unique.
 * @property steps - Ordered array of `TutorialStep` definitions that make
 *   up the tutorial content. Each step has an explanation, exercise, hints,
 *   and success message.
 * @property completionLink - Navigation target shown when the user finishes
 *   the last step. Contains an `href` (URL) and `label` (button text).
 *   Typically points to the next tutorial in the curriculum sequence.
 */
export interface TutorialConfig {
  slug: string;
  title: string;
  storageKey: string;
  steps: TutorialStep[];
  completionLink: { href: string; label: string };
}

/* ------------------------------------------------------------------ */
/*  Tutorial registry                                                  */
/* ------------------------------------------------------------------ */

/**
 * The master list of all tutorials, ordered by curriculum sequence.
 *
 * The ordering matters for the tutorial index page and the chained
 * `completionLink` navigation. Each tutorial's `completionLink.href`
 * points to the next entry in this array, forming a linear progression
 * through the entire Software Foundations-inspired curriculum.
 *
 * Volumes:
 *   - Logical Foundations (LF): basics -> applied-methods -> logic-negation
 *     -> proof-strategies -> polymorphism -> inductive-props
 *   - Programming Language Foundations (PLF): defining-languages -> type-systems
 *   - Verified Functional Algorithms (VFA): verified-sorting -> verified-data-structures
 *   - Security Foundations (SecF): security-noninterference -> security-ifc
 *     -> security-constant-time
 */
export const tutorials: TutorialConfig[] = [
  {
    slug: 'basics',
    title: 'Tutorial: Basics',
    storageKey: 'leetmethods-tutorial-progress',
    steps: tutorialSteps,
    completionLink: { href: '/tutorial/applied-methods', label: 'Continue to Applied Methods' },
  },
  {
    slug: 'applied-methods',
    title: 'Tutorial: Applied Methods',
    storageKey: 'leetmethods-applied-methods-progress',
    steps: appliedMethodsSteps,
    completionLink: { href: '/tutorial/logic-negation', label: 'Continue to Logic & Negation' },
  },
  {
    slug: 'logic-negation',
    title: 'Tutorial: Logic & Negation',
    storageKey: 'leetmethods-logic-negation-progress',
    steps: logicNegationSteps,
    completionLink: { href: '/tutorial/proof-strategies', label: 'Continue to Proof Strategies' },
  },
  {
    slug: 'proof-strategies',
    title: 'Tutorial: Proof Strategies',
    storageKey: 'leetmethods-proof-strategies-progress',
    steps: proofStrategiesSteps,
    completionLink: { href: '/tutorial/polymorphism', label: 'Continue to Polymorphism' },
  },
  {
    slug: 'polymorphism',
    title: 'Tutorial: Polymorphism & Higher-Order Functions',
    storageKey: 'leetmethods-polymorphism-progress',
    steps: polymorphismSteps,
    completionLink: { href: '/tutorial/inductive-props', label: 'Continue to Inductive Propositions' },
  },
  {
    slug: 'inductive-props',
    title: 'Tutorial: Inductive Propositions',
    storageKey: 'leetmethods-inductive-props-progress',
    steps: inductivePropsSteps,
    completionLink: { href: '/tutorial/defining-languages', label: 'Continue to Defining Languages' },
  },
  {
    slug: 'defining-languages',
    title: 'Tutorial: Defining Languages',
    storageKey: 'leetmethods-defining-languages-progress',
    steps: definingLanguagesSteps,
    completionLink: { href: '/tutorial/type-systems', label: 'Continue to Type Systems' },
  },
  {
    slug: 'type-systems',
    title: 'Tutorial: Type Systems',
    storageKey: 'leetmethods-type-systems-progress',
    steps: typeSystemsSteps,
    completionLink: { href: '/tutorial/verified-sorting', label: 'Continue to Verified Sorting' },
  },
  {
    slug: 'verified-sorting',
    title: 'Tutorial: Verified Sorting',
    storageKey: 'leetmethods-verified-sorting-progress',
    steps: verifiedSortingSteps,
    completionLink: { href: '/tutorial/verified-data-structures', label: 'Continue to Verified Data Structures' },
  },
  {
    slug: 'verified-data-structures',
    title: 'Tutorial: Verified Data Structures',
    storageKey: 'leetmethods-verified-data-structures-progress',
    steps: verifiedDataStructuresSteps,
    completionLink: { href: '/tutorial/security-noninterference', label: 'Continue to Security Foundations' },
  },
  {
    slug: 'security-noninterference',
    title: 'Tutorial: Noninterference & Secrecy',
    storageKey: 'leetmethods-security-noninterference-progress',
    steps: securityNoninterferenceSteps,
    completionLink: { href: '/tutorial/security-ifc', label: 'Continue to Security Type Systems' },
  },
  {
    slug: 'security-ifc',
    title: 'Tutorial: Security Type Systems',
    storageKey: 'leetmethods-security-ifc-progress',
    steps: securityIfcSteps,
    completionLink: { href: '/tutorial/security-constant-time', label: 'Continue to Constant-Time Programming' },
  },
  {
    slug: 'security-constant-time',
    title: 'Tutorial: Constant-Time Programming',
    storageKey: 'leetmethods-security-ct-progress',
    steps: securityConstantTimeSteps,
    /**
     * Final tutorial in the curriculum. Points to `/learn` (Learning Paths)
     * as the natural next step after completing all tutorials.
     */
    completionLink: { href: '/learn', label: 'Start Learning Paths' },
  },
];

/* ------------------------------------------------------------------ */
/*  Lookup helpers                                                     */
/* ------------------------------------------------------------------ */

/**
 * Finds a tutorial configuration by its URL slug.
 *
 * Used by the `/tutorial/[slug]` dynamic route to resolve the tutorial
 * data for a given URL. Returns `undefined` if no tutorial with the
 * given slug is registered, which triggers a 404 in the page component.
 *
 * @param slug - The URL slug to look up (e.g., 'basics', 'polymorphism').
 * @returns The matching `TutorialConfig`, or `undefined` if not found.
 */
export function getTutorialBySlug(slug: string): TutorialConfig | undefined {
  return tutorials.find((t) => t.slug === slug);
}

/**
 * Returns an array of all registered tutorial slugs.
 *
 * Useful for generating static params, building navigation menus, or
 * validating that a slug exists without loading the full tutorial config.
 *
 * @returns An array of slug strings in curriculum order.
 */
export function getAllTutorialSlugs(): string[] {
  return tutorials.map((t) => t.slug);
}
