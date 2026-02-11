/**
 * @module RootLayout
 *
 * The top-level layout for the entire LeetMethods application, rendered at `/`.
 *
 * This file fulfills the Next.js App Router requirement of a root `layout.tsx`
 * that provides the `<html>` and `<body>` elements. It is a **server component**
 * and wraps every page in the application.
 *
 * Responsibilities:
 * - Loads and applies the Geist Sans and Geist Mono variable fonts via
 *   `next/font/local`. These fonts are referenced in CSS via the custom
 *   properties `--font-geist-sans` and `--font-geist-mono`.
 * - Provides the `ThemeProvider` (dark/light mode support via next-themes)
 *   around the entire app.
 * - Renders the global `Navbar` at the top and the `AchievementToast`
 *   overlay, which shows toast notifications when the user unlocks achievements.
 * - Sets the `suppressHydrationWarning` attribute on `<html>` because
 *   next-themes injects a `class` attribute during SSR that may differ from
 *   the client's preference, which would otherwise trigger a React hydration
 *   mismatch warning.
 * - Defines site-wide `<title>` and `<meta name="description">` via the
 *   exported `metadata` object.
 *
 * Note: Security headers (COEP, COOP, CSP) are configured in
 * `next.config.mjs`, not here.
 */

import type { Metadata } from 'next';
import localFont from 'next/font/local';
import { ThemeProvider } from '@/components/theme-provider';
import { Navbar } from '@/components/navbar';
import { AchievementToast } from '@/components/achievements/AchievementToast';
import './globals.css';

/* ------------------------------------------------------------------ */
/*  Font configuration                                                 */
/* ------------------------------------------------------------------ */

/**
 * Geist Sans variable font loaded from a local `.woff` file.
 * Exposes the CSS custom property `--font-geist-sans` for use in Tailwind
 * or custom CSS rules. Weight range 100-900 covers all standard weights.
 */
const geistSans = localFont({
  src: './fonts/GeistVF.woff',
  variable: '--font-geist-sans',
  weight: '100 900',
});

/**
 * Geist Mono variable font loaded from a local `.woff` file.
 * Used primarily for the Coq code editor (CodeMirror) and any inline
 * `<code>` elements. Exposes `--font-geist-mono`.
 */
const geistMono = localFont({
  src: './fonts/GeistMonoVF.woff',
  variable: '--font-geist-mono',
  weight: '100 900',
});

/* ------------------------------------------------------------------ */
/*  Metadata                                                           */
/* ------------------------------------------------------------------ */

/**
 * Next.js static metadata object. Sets the default `<title>` and
 * `<meta name="description">` for every page unless overridden by a
 * more specific layout or page-level `metadata` export.
 */
export const metadata: Metadata = {
  title: 'LeetMethods - Practice Coq Proofs',
  description: 'An interactive platform for practicing formal proofs in Coq',
};

/* ------------------------------------------------------------------ */
/*  Layout component                                                   */
/* ------------------------------------------------------------------ */

/**
 * Root layout component that wraps every page in the application.
 *
 * The component tree is:
 *   `<html>` -> `<body>` -> `ThemeProvider` -> flex container
 *     -> `Navbar` (sticky top navigation)
 *     -> `<main>` (page content via `children`)
 *     -> `AchievementToast` (portal-like overlay for achievement popups)
 *
 * The `flex flex-col min-h-screen` pattern on the wrapper div ensures the
 * footer (if present in child pages) is pushed to the bottom of the viewport
 * even when page content is short.
 *
 * @param props.children - The page-level React tree injected by the App Router.
 * @returns The full HTML document shell.
 */
export default function RootLayout({
  children,
}: {
  children: React.ReactNode;
}) {
  return (
    <html lang="en" suppressHydrationWarning>
      <body className={`${geistSans.variable} ${geistMono.variable} antialiased`}>
        <ThemeProvider>
          <div className="min-h-screen flex flex-col">
            <Navbar />
            <main className="flex-1">{children}</main>
            <AchievementToast />
          </div>
        </ThemeProvider>
      </body>
    </html>
  );
}
