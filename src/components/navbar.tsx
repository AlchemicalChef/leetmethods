'use client';

import { useState } from 'react';
import Link from 'next/link';
import { BookOpen, ChevronDown, Code2, FlaskConical, GraduationCap, Menu, X, BarChart3, PlusCircle } from 'lucide-react';
import { ThemeToggle } from '@/components/theme-toggle';
import { Button } from '@/components/ui/button';
import {
  DropdownMenu,
  DropdownMenuContent,
  DropdownMenuItem,
  DropdownMenuTrigger,
} from '@/components/ui/dropdown-menu';

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
                  Basics
                </Link>
              </DropdownMenuItem>
              <DropdownMenuItem asChild>
                <Link href="/tutorial/applied-methods" className="flex items-center gap-2">
                  <FlaskConical className="h-4 w-4" />
                  Applied Methods
                </Link>
              </DropdownMenuItem>
            </DropdownMenuContent>
          </DropdownMenu>
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
              <DropdownMenuItem asChild>
                <Link href="/problems/custom/create" className="flex items-center gap-2">
                  <PlusCircle className="h-4 w-4" />
                  Create Problem
                </Link>
              </DropdownMenuItem>
            </DropdownMenuContent>
          </DropdownMenu>
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
              Tutorial: Basics
            </Link>
            <Link
              href="/tutorial/applied-methods"
              className="block text-sm font-medium text-muted-foreground hover:text-foreground transition-colors py-2 flex items-center gap-2 pl-6"
              onClick={() => setMobileMenuOpen(false)}
            >
              <FlaskConical className="h-4 w-4" />
              Applied Methods
            </Link>
            <Link
              href="/problems"
              className="block text-sm font-medium text-muted-foreground hover:text-foreground transition-colors py-2"
              onClick={() => setMobileMenuOpen(false)}
            >
              Problems
            </Link>
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
