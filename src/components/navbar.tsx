'use client';

import { useState } from 'react';
import Link from 'next/link';
import { BookOpen, Code2, GraduationCap, Menu, X, BarChart3 } from 'lucide-react';
import { ThemeToggle } from '@/components/theme-toggle';
import { Button } from '@/components/ui/button';

export function Navbar() {
  const [mobileMenuOpen, setMobileMenuOpen] = useState(false);

  return (
    <header className="border-b bg-background/95 backdrop-blur supports-[backdrop-filter]:bg-background/60 sticky top-0 z-50">
      <nav className="max-w-7xl mx-auto px-4 h-16 flex items-center justify-between">
        <Link href="/" className="flex items-center gap-2 font-bold text-xl">
          <Code2 className="h-6 w-6 text-primary" />
          <span className="hidden sm:inline">LeetMethods</span>
          <span className="sm:hidden">LM</span>
        </Link>

        {/* Desktop navigation */}
        <div className="hidden md:flex items-center gap-6">
          <Link
            href="/tutorial"
            className="text-sm font-medium text-muted-foreground hover:text-foreground transition-colors flex items-center gap-1"
          >
            <GraduationCap className="h-4 w-4" />
            Tutorial
          </Link>
          <Link
            href="/problems"
            className="text-sm font-medium text-muted-foreground hover:text-foreground transition-colors"
          >
            Problems
          </Link>
          <Link
            href="/learn"
            className="text-sm font-medium text-muted-foreground hover:text-foreground transition-colors flex items-center gap-1"
          >
            <BookOpen className="h-4 w-4" />
            Learn
          </Link>
          <Link
            href="/stats"
            className="text-sm font-medium text-muted-foreground hover:text-foreground transition-colors flex items-center gap-1"
          >
            <BarChart3 className="h-4 w-4" />
            Stats
          </Link>
          <ThemeToggle />
        </div>

        {/* Mobile menu button */}
        <div className="flex items-center gap-2 md:hidden">
          <ThemeToggle />
          <Button
            variant="ghost"
            size="icon"
            onClick={() => setMobileMenuOpen(!mobileMenuOpen)}
            aria-label="Toggle menu"
          >
            {mobileMenuOpen ? <X className="h-5 w-5" /> : <Menu className="h-5 w-5" />}
          </Button>
        </div>
      </nav>

      {/* Mobile menu */}
      {mobileMenuOpen && (
        <div className="md:hidden border-t bg-background">
          <div className="px-4 py-3 space-y-3">
            <Link
              href="/tutorial"
              className="block text-sm font-medium text-muted-foreground hover:text-foreground transition-colors py-2 flex items-center gap-2"
              onClick={() => setMobileMenuOpen(false)}
            >
              <GraduationCap className="h-4 w-4" />
              Tutorial
            </Link>
            <Link
              href="/problems"
              className="block text-sm font-medium text-muted-foreground hover:text-foreground transition-colors py-2"
              onClick={() => setMobileMenuOpen(false)}
            >
              Problems
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
