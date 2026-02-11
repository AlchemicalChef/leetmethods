/**
 * @module TutorialLayout
 *
 * Next.js App Router layout for the `/tutorial` route segment and all its
 * children (including `/tutorial/[slug]`).
 *
 * This layout serves two purposes:
 *
 * 1. **Metadata**: Exports a static `metadata` object that sets the page
 *    title and description for all tutorial routes. Individual tutorial
 *    pages (e.g., `/tutorial/basics`) inherit this metadata unless they
 *    provide their own. Since the dynamic `[slug]/page.tsx` is a client
 *    component and cannot export `metadata`, this layout is the primary
 *    place where tutorial SEO metadata is defined.
 *
 * 2. **Pass-through rendering**: The layout itself is a transparent
 *    wrapper -- it simply renders `{children}` without adding any
 *    additional DOM structure. This is the minimal pattern for a
 *    "metadata-only" layout in the App Router. If tutorial-specific
 *    chrome (e.g., a sidebar, breadcrumbs) were needed, it would be
 *    added here.
 *
 * This is a **server component** (no 'use client') since it only provides
 * metadata and renders children without any interactivity.
 */

import type { Metadata } from 'next';

/**
 * Static metadata shared by all pages under the `/tutorial` route segment.
 * Provides a meaningful tab title and SEO description for the tutorial section.
 */
export const metadata: Metadata = {
  title: 'Tutorial | LeetMethods',
  description: 'Learn the basics of theorem proving in Coq with step-by-step interactive exercises.',
};

/**
 * Tutorial layout component.
 *
 * Acts as a transparent pass-through, rendering child pages without
 * adding any wrapping DOM elements. Its primary purpose is to host
 * the `metadata` export above.
 *
 * @param props.children - The tutorial page content injected by the App Router.
 * @returns The children directly, with no additional wrapper elements.
 */
export default function TutorialLayout({ children }: { children: React.ReactNode }) {
  return children;
}
