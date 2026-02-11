/**
 * @module ThemeToggle
 *
 * Dropdown button component for switching between light, dark, and system themes.
 *
 * Renders a button with animated Sun/Moon icons that swap based on the current
 * theme, and a dropdown menu with three options (Light, Dark, System) that each
 * show an "Active" indicator when selected.
 *
 * Design decisions:
 *   - **Hydration safety**: The component uses a `mounted` state flag that
 *     flips to `true` after the first client-side render. Before mounting,
 *     the theme value from `next-themes` may not match the server-rendered
 *     output (since the theme is stored in localStorage), which would cause
 *     a hydration mismatch. The pre-mount state renders a disabled button
 *     placeholder to avoid this.
 *   - **Icon animation**: The Sun and Moon icons use CSS rotate/scale
 *     transitions that cross-fade based on the `dark` class. In light mode,
 *     the Sun is visible (scale-100, rotate-0) and the Moon is hidden
 *     (scale-0, rotate-90). In dark mode, these are reversed. The Moon is
 *     positioned absolutely to overlap the Sun's position.
 *   - **Active indicator**: Each dropdown item shows "Active" text when it
 *     matches the current theme, giving clear feedback about the current
 *     selection.
 *
 * @see ThemeProvider - The context provider that manages theme state
 */
'use client';

import * as React from 'react';
import { Moon, Sun, Monitor } from 'lucide-react';
import { useTheme } from 'next-themes';

import { Button } from '@/components/ui/button';
import {
  DropdownMenu,
  DropdownMenuContent,
  DropdownMenuItem,
  DropdownMenuTrigger,
} from '@/components/ui/dropdown-menu';

/**
 * Renders a theme toggle button with a dropdown menu for selecting
 * light, dark, or system theme.
 *
 * @returns A dropdown menu button for theme selection, or a disabled
 *   placeholder during SSR/initial hydration.
 */
export function ThemeToggle() {
  const { setTheme, theme } = useTheme();

  /**
   * Mounted flag to prevent hydration mismatches.
   * `next-themes` reads the theme from localStorage on the client, which
   * may differ from what the server rendered. By only rendering the full
   * component after mount, we avoid React hydration warnings.
   */
  const [mounted, setMounted] = React.useState(false);

  React.useEffect(() => {
    setMounted(true);
  }, []);

  /* Pre-mount placeholder: a disabled button with a static Sun icon.
     This matches the server-rendered output and prevents layout shift. */
  if (!mounted) {
    return (
      <Button variant="ghost" size="icon" disabled>
        <Sun className="h-5 w-5" />
        <span className="sr-only">Toggle theme</span>
      </Button>
    );
  }

  return (
    <DropdownMenu>
      <DropdownMenuTrigger asChild>
        <Button variant="ghost" size="icon">
          {/* Sun icon: visible in light mode, hidden in dark mode via CSS transitions.
              The rotate and scale transitions create a smooth cross-fade effect. */}
          <Sun className="h-5 w-5 rotate-0 scale-100 transition-all dark:-rotate-90 dark:scale-0" />
          {/* Moon icon: positioned absolutely to overlap the Sun.
              Hidden in light mode (scale-0, rotate-90), visible in dark mode. */}
          <Moon className="absolute h-5 w-5 rotate-90 scale-0 transition-all dark:rotate-0 dark:scale-100" />
          <span className="sr-only">Toggle theme</span>
        </Button>
      </DropdownMenuTrigger>
      <DropdownMenuContent align="end">
        {/* Light theme option */}
        <DropdownMenuItem onClick={() => setTheme('light')}>
          <Sun className="mr-2 h-4 w-4" />
          <span>Light</span>
          {theme === 'light' && <span className="ml-auto text-xs">Active</span>}
        </DropdownMenuItem>
        {/* Dark theme option */}
        <DropdownMenuItem onClick={() => setTheme('dark')}>
          <Moon className="mr-2 h-4 w-4" />
          <span>Dark</span>
          {theme === 'dark' && <span className="ml-auto text-xs">Active</span>}
        </DropdownMenuItem>
        {/* System theme option -- follows OS preference */}
        <DropdownMenuItem onClick={() => setTheme('system')}>
          <Monitor className="mr-2 h-4 w-4" />
          <span>System</span>
          {theme === 'system' && <span className="ml-auto text-xs">Active</span>}
        </DropdownMenuItem>
      </DropdownMenuContent>
    </DropdownMenu>
  );
}
