/**
 * @module KeyboardShortcutsHelp
 *
 * A dialog component that displays all available keyboard shortcuts for
 * the Coq editor and general application navigation.
 *
 * This help dialog is triggered by:
 * - Pressing '?' anywhere outside the editor or input fields
 * - Clicking the help button (?) in the EditorToolbar
 *
 * The shortcuts are organized into categories:
 * - **Execution**: Coq statement navigation (Alt+N, Alt+P, Alt+Enter, etc.)
 * - **Editor**: Standard text editing (undo, redo, select all)
 * - **General**: Application shortcuts (this help dialog)
 *
 * Design decisions:
 * - Platform detection (`isMac`) is done at module scope to determine whether
 *   to show "Cmd" or "Ctrl" as the modifier key. This runs once and uses
 *   `navigator.platform` with a `typeof navigator` guard for SSR safety.
 * - Shortcuts support an `altKeys` field for alternative bindings (e.g.,
 *   Alt+N and Alt+Down both execute the next statement), shown with "or."
 * - The KeyCombo sub-component renders individual key badges with `<kbd>`
 *   elements for proper semantics and consistent visual styling.
 * - The shortcuts data structure is defined as a module-level constant since
 *   it never changes at runtime.
 *
 * @see {@link CoqEditor} for the keybinding implementations
 * @see {@link ProblemSolver} for the '?' key listener that opens this dialog
 */
'use client';

import { Dialog } from '@/components/ui/dialog';

/* ============================================================================
 * Types
 * ============================================================================ */

/**
 * Props for the KeyboardShortcutsHelp dialog.
 */
interface KeyboardShortcutsHelpProps {
  /** Whether the dialog is currently open */
  open: boolean;
  /** Callback to close the dialog */
  onClose: () => void;
}

/**
 * Represents a single keyboard shortcut with primary keys and optional
 * alternative keys (both shown in the UI separated by "or").
 */
interface ShortcutItem {
  /** Primary key combination (e.g., ['Alt', 'N']) */
  keys: string[];
  /** Alternative key combination, if any (e.g., ['Alt', '↓']) */
  altKeys?: string[];
  /** Human-readable description of what the shortcut does */
  description: string;
}

/* ============================================================================
 * Platform Detection & Shortcut Data
 * ============================================================================ */

/**
 * Detect macOS to show the correct modifier symbol.
 * Uses `navigator.platform` with a typeof guard for server-side rendering
 * where `navigator` is undefined.
 */
const isMac = typeof navigator !== 'undefined' && /Mac|iPod|iPhone|iPad/.test(navigator.platform);

/** The platform-appropriate modifier key symbol (Cmd on Mac, Ctrl elsewhere) */
const mod = isMac ? '⌘' : 'Ctrl';

/**
 * All keyboard shortcuts organized by category.
 *
 * This is a static data structure -- shortcuts do not change at runtime.
 * Each category contains a label and an array of shortcut items.
 */
const shortcuts: { category: string; items: ShortcutItem[] }[] = [
  {
    category: 'Execution',
    items: [
      { keys: ['Alt', 'N'], altKeys: ['Alt', '↓'], description: 'Execute next statement' },
      { keys: ['Alt', 'P'], altKeys: ['Alt', '↑'], description: 'Undo last statement' },
      { keys: ['Alt', 'Enter'], altKeys: ['Alt', '→'], description: 'Execute all statements' },
    ],
  },
  {
    category: 'Editor',
    items: [
      { keys: [mod, 'Z'], description: 'Undo edit' },
      { keys: [mod, 'Shift', 'Z'], description: 'Redo edit' },
      { keys: [mod, 'A'], description: 'Select all' },
    ],
  },
  {
    category: 'General',
    items: [
      { keys: ['?'], description: 'Show keyboard shortcuts' },
    ],
  },
];

/* ============================================================================
 * KeyboardShortcutsHelp Component
 * ============================================================================ */

/**
 * Modal dialog displaying all keyboard shortcuts grouped by category.
 *
 * @param props - See {@link KeyboardShortcutsHelpProps}
 * @returns The shortcuts help dialog
 */
export function KeyboardShortcutsHelp({ open, onClose }: KeyboardShortcutsHelpProps) {
  return (
    <Dialog open={open} onClose={onClose} title="Keyboard Shortcuts">
      <div className="space-y-6">
        {shortcuts.map((section) => (
          <div key={section.category}>
            {/* Category header (e.g., "EXECUTION", "EDITOR") */}
            <h3 className="text-sm font-semibold text-muted-foreground uppercase tracking-wider mb-3">
              {section.category}
            </h3>
            <div className="space-y-2">
              {section.items.map((shortcut) => (
                <div
                  key={shortcut.description}
                  className="flex items-center justify-between py-1.5"
                >
                  {/* Shortcut description on the left */}
                  <span className="text-sm">{shortcut.description}</span>
                  {/* Key combos on the right, with optional alternative */}
                  <div className="flex items-center gap-2">
                    <KeyCombo keys={shortcut.keys} />
                    {shortcut.altKeys && (
                      <>
                        <span className="text-xs text-muted-foreground">or</span>
                        <KeyCombo keys={shortcut.altKeys} />
                      </>
                    )}
                  </div>
                </div>
              ))}
            </div>
          </div>
        ))}
      </div>
    </Dialog>
  );
}

/* ============================================================================
 * KeyCombo Sub-component
 * ============================================================================ */

/**
 * Renders a series of keyboard keys with '+' separators.
 *
 * Uses semantic `<kbd>` elements styled as small rounded badges to match
 * the visual language of keyboard shortcuts in desktop applications.
 *
 * @param props.keys - Array of key labels (e.g., ['Alt', 'N'])
 */
function KeyCombo({ keys }: { keys: string[] }) {
  return (
    <div className="flex items-center gap-1">
      {keys.map((key, i) => (
        <span key={i}>
          {/* Show '+' separator between keys (not before the first one) */}
          {i > 0 && <span className="text-muted-foreground mx-0.5">+</span>}
          <kbd className="inline-flex items-center justify-center min-w-[24px] px-1.5 py-0.5 text-xs font-mono bg-muted border rounded shadow-sm">
            {key}
          </kbd>
        </span>
      ))}
    </div>
  );
}
