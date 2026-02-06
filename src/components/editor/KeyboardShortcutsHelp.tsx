'use client';

import { Dialog } from '@/components/ui/dialog';

interface KeyboardShortcutsHelpProps {
  open: boolean;
  onClose: () => void;
}

interface ShortcutItem {
  keys: string[];
  altKeys?: string[];
  description: string;
}

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
      { keys: ['Ctrl', 'Z'], description: 'Undo edit' },
      { keys: ['Ctrl', 'Shift', 'Z'], description: 'Redo edit' },
      { keys: ['Ctrl', 'A'], description: 'Select all' },
    ],
  },
  {
    category: 'General',
    items: [
      { keys: ['?'], description: 'Show keyboard shortcuts' },
    ],
  },
];

export function KeyboardShortcutsHelp({ open, onClose }: KeyboardShortcutsHelpProps) {
  return (
    <Dialog open={open} onClose={onClose} title="Keyboard Shortcuts">
      <div className="space-y-6">
        {shortcuts.map((section) => (
          <div key={section.category}>
            <h3 className="text-sm font-semibold text-muted-foreground uppercase tracking-wider mb-3">
              {section.category}
            </h3>
            <div className="space-y-2">
              {section.items.map((shortcut) => (
                <div
                  key={shortcut.description}
                  className="flex items-center justify-between py-1.5"
                >
                  <span className="text-sm">{shortcut.description}</span>
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

function KeyCombo({ keys }: { keys: string[] }) {
  return (
    <div className="flex items-center gap-1">
      {keys.map((key, i) => (
        <span key={i}>
          {i > 0 && <span className="text-muted-foreground mx-0.5">+</span>}
          <kbd className="inline-flex items-center justify-center min-w-[24px] px-1.5 py-0.5 text-xs font-mono bg-muted border rounded shadow-sm">
            {key}
          </kbd>
        </span>
      ))}
    </div>
  );
}
