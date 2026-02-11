/**
 * @module ThemeProvider
 *
 * Application-level theme provider that wraps the entire component tree
 * to enable dark mode, light mode, and system-preference-based theming.
 *
 * This is a thin wrapper around `next-themes`'s ThemeProvider configured
 * with the following settings:
 *   - `attribute="class"` -- Theme is applied by adding a class (e.g., "dark")
 *     to the `<html>` element, which integrates with Tailwind CSS's dark mode
 *     class strategy.
 *   - `defaultTheme="system"` -- New users get the theme matching their OS
 *     preference (prefers-color-scheme media query).
 *   - `enableSystem` -- Allows the "system" option that automatically follows
 *     the user's OS-level light/dark preference.
 *   - `disableTransitionOnChange` -- Prevents a flash of transition animations
 *     when switching themes. Without this, all elements with CSS transitions
 *     would briefly animate their color changes, creating a distracting effect.
 *
 * This component must be a client component because `next-themes` uses
 * React context and client-side APIs (localStorage, matchMedia) to manage
 * theme state.
 *
 * @see ThemeToggle - The UI component that lets users switch between themes
 */
'use client';

import * as React from 'react';
import { ThemeProvider as NextThemesProvider } from 'next-themes';

/**
 * Wraps children with the next-themes ThemeProvider configured for
 * Tailwind CSS class-based dark mode with system preference support.
 *
 * @param props.children - The React component tree to wrap with theme context.
 * @returns The theme provider wrapping the children.
 */
export function ThemeProvider({ children }: { children: React.ReactNode }) {
  return (
    <NextThemesProvider
      attribute="class"
      defaultTheme="system"
      enableSystem
      disableTransitionOnChange
    >
      {children}
    </NextThemesProvider>
  );
}
