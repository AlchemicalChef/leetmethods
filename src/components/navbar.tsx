/**
 * @module Navbar
 *
 * Top-level navigation bar component used across all pages in the app.
 *
 * Implements a responsive navigation pattern:
 *   - **Desktop (md+)**: Horizontal nav with dropdown menus for Tutorial
 *     and Problems sections, plus direct links for Learn and Stats.
 *   - **Mobile (<md)**: Hamburger menu button that toggles a full-width
 *     vertical menu below the header.
 *
 * The navbar is sticky-positioned at the top of the viewport with a
 * semi-transparent backdrop blur effect, allowing content to scroll
 * beneath it while maintaining readability.
 *
 * Design decisions:
 *   - Dropdown menus use Radix UI's DropdownMenu (via shadcn/ui) for
 *     accessible keyboard navigation and focus management.
 *   - The mobile menu is a simple boolean toggle (no animation) for
 *     simplicity. Each mobile link calls `setMobileMenuOpen(false)`
 *     on click to close the menu after navigation.
 *   - The logo shows "LeetMethods" on screens >= sm (640px) and abbreviates
 *     to "LM" on smaller screens to save horizontal space.
 *   - The ThemeToggle is placed in both the desktop nav and the mobile
 *     menu button area so it is always accessible regardless of screen size.
 *   - z-50 ensures the navbar sits above page content but below modals
 *     (which use z-100+) and achievement toasts (z-200).
 */
'use client';

import { useState } from 'react';
import Link from 'next/link';
import { BookOpen, ChevronDown, Code2, GraduationCap, Menu, X, BarChart3, PlusCircle } from 'lucide-react';
import { ThemeToggle } from '@/components/theme-toggle';
import { Button } from '@/components/ui/button';
import {
  DropdownMenu,
  DropdownMenuContent,
  DropdownMenuItem,
  DropdownMenuTrigger,
} from '@/components/ui/dropdown-menu';

/**
 * Renders the site-wide navigation bar with responsive desktop and mobile layouts.
 *
 * @returns The sticky header element containing all navigation elements.
 */
export function Navbar() {
  /** Controls whether the mobile menu panel is visible */
  const [mobileMenuOpen, setMobileMenuOpen] = useState(false);

  return (
    <header className="border-b bg-background/95 backdrop-blur supports-[backdrop-filter]:bg-background/60 sticky top-0 z-50">
      <nav className="max-w-7xl mx-auto px-4 h-16 flex items-center justify-between">
        {/* Logo/home link -- full name on sm+ screens, abbreviation on mobile */}
        <Link href="/" className="flex items-center gap-2 font-bold text-xl">
          <Code2 className="h-6 w-6 text-primary" />
          <span className="hidden sm:inline">LeetMethods</span>
          <span className="sm:hidden">LM</span>
        </Link>

        {/* ================================================================
         * Desktop navigation (hidden on mobile)
         * Uses dropdown menus for Tutorial and Problems sections,
         * and direct links for Learn and Stats.
         * ================================================================ */}
        <div className="hidden md:flex items-center gap-6">
          {/* Tutorial dropdown menu */}
          <DropdownMenu>
            <DropdownMenuTrigger asChild>
              <button className="text-sm font-medium text-muted-foreground hover:text-foreground transition-colors flex items-center gap-1">
                <GraduationCap className="h-4 w-4" />
                Tutorial
                <ChevronDown className="h-3 w-3" />
              </button>
            </DropdownMenuTrigger>
            <DropdownMenuContent align="start">
              <DropdownMenuItem asChild>
                <Link href="/tutorial" className="flex items-center gap-2">
                  <GraduationCap className="h-4 w-4" />
                  All Tutorials
                </Link>
              </DropdownMenuItem>
              {/* Quick-start link to the basics tutorial for new users */}
              <DropdownMenuItem asChild>
                <Link href="/tutorial/basics" className="flex items-center gap-2 pl-6">
                  Start: Basics
                </Link>
              </DropdownMenuItem>
            </DropdownMenuContent>
          </DropdownMenu>

          {/* Problems dropdown menu */}
          <DropdownMenu>
            <DropdownMenuTrigger asChild>
              <button className="text-sm font-medium text-muted-foreground hover:text-foreground transition-colors flex items-center gap-1">
                Problems
                <ChevronDown className="h-3 w-3" />
              </button>
            </DropdownMenuTrigger>
            <DropdownMenuContent align="start">
              <DropdownMenuItem asChild>
                <Link href="/problems" className="flex items-center gap-2">
                  <Code2 className="h-4 w-4" />
                  Browse Problems
                </Link>
              </DropdownMenuItem>
              {/* Link to create a custom problem */}
              <DropdownMenuItem asChild>
                <Link href="/problems/custom/create" className="flex items-center gap-2">
                  <PlusCircle className="h-4 w-4" />
                  Create Problem
                </Link>
              </DropdownMenuItem>
            </DropdownMenuContent>
          </DropdownMenu>

          {/* Direct link to the Learn page */}
          <Link
            href="/learn"
            className="text-sm font-medium text-muted-foreground hover:text-foreground transition-colors flex items-center gap-1"
          >
            <BookOpen className="h-4 w-4" />
            Learn
          </Link>

          {/* Direct link to the Stats page */}
          <Link
            href="/stats"
            className="text-sm font-medium text-muted-foreground hover:text-foreground transition-colors flex items-center gap-1"
          >
            <BarChart3 className="h-4 w-4" />
            Stats
          </Link>

          {/* Theme toggle (light/dark/system) for desktop */}
          <ThemeToggle />
        </div>

        {/* ================================================================
         * Mobile menu button area (hidden on desktop)
         * Contains the theme toggle and hamburger/close toggle button.
         * ================================================================ */}
        <div className="flex items-center gap-2 md:hidden">
          {/* Theme toggle always accessible on mobile */}
          <ThemeToggle />
          <Button
            variant="ghost"
            size="icon"
            onClick={() => setMobileMenuOpen(!mobileMenuOpen)}
            aria-label="Toggle menu"
          >
            {/* Swap between hamburger (Menu) and close (X) icons */}
            {mobileMenuOpen ? <X className="h-5 w-5" /> : <Menu className="h-5 w-5" />}
          </Button>
        </div>
      </nav>

      {/* ================================================================
       * Mobile menu panel (hidden on desktop)
       * Full-width dropdown panel that appears below the header when the
       * hamburger menu is toggled. Each link closes the menu on click to
       * avoid the menu staying open after navigation.
       * ================================================================ */}
      {mobileMenuOpen && (
        <div className="md:hidden border-t bg-background">
          <div className="px-4 py-3 space-y-3">
            <Link
              href="/tutorial"
              className="block text-sm font-medium text-muted-foreground hover:text-foreground transition-colors py-2 flex items-center gap-2"
              onClick={() => setMobileMenuOpen(false)}
            >
              <GraduationCap className="h-4 w-4" />
              Tutorials
            </Link>
            <Link
              href="/problems"
              className="block text-sm font-medium text-muted-foreground hover:text-foreground transition-colors py-2"
              onClick={() => setMobileMenuOpen(false)}
            >
              Problems
            </Link>
            {/* Indented sub-link for creating custom problems */}
            <Link
              href="/problems/custom/create"
              className="block text-sm font-medium text-muted-foreground hover:text-foreground transition-colors py-2 flex items-center gap-2 pl-6"
              onClick={() => setMobileMenuOpen(false)}
            >
              <PlusCircle className="h-4 w-4" />
              Create Problem
            </Link>
            <Link
              href="/learn"
              className="block text-sm font-medium text-muted-foreground hover:text-foreground transition-colors py-2 flex items-center gap-2"
              onClick={() => setMobileMenuOpen(false)}
            >
              <BookOpen className="h-4 w-4" />
              Learn
            </Link>
            <Link
              href="/stats"
              className="block text-sm font-medium text-muted-foreground hover:text-foreground transition-colors py-2 flex items-center gap-2"
              onClick={() => setMobileMenuOpen(false)}
            >
              <BarChart3 className="h-4 w-4" />
              Stats
            </Link>
          </div>
        </div>
      )}
    </header>
  );
}
