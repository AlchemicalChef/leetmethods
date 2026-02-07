'use client';

import { useEffect, useRef, useMemo, useState } from 'react';
import { EditorState, StateEffect, StateField, Compartment, type Range } from '@codemirror/state';
import { EditorView, Decoration, keymap, lineNumbers, highlightActiveLine, highlightActiveLineGutter } from '@codemirror/view';
import { defaultKeymap, history, historyKeymap } from '@codemirror/commands';
import { syntaxHighlighting, defaultHighlightStyle, bracketMatching } from '@codemirror/language';
import { oneDark } from '@codemirror/theme-one-dark';
import { useTheme } from 'next-themes';
import { coqLanguage } from '@/lib/coq/coq-syntax';
import { coqAutocomplete } from '@/lib/coq/coq-autocomplete';
import { coqHoverTooltip } from '@/lib/coq/coq-hover';

// Execution highlight decorations
const setExecutedUpTo = StateEffect.define<number>();

const executedLineDeco = Decoration.line({ class: 'cm-executed-line' });

const executedField = StateField.define({
  create() {
    return Decoration.none;
  },
  update(decos, tr) {
    for (const effect of tr.effects) {
      if (effect.is(setExecutedUpTo)) {
        const offset = effect.value;
        if (offset <= 0) return Decoration.none;
        const doc = tr.state.doc;
        const endLine = doc.lineAt(Math.min(offset, doc.length)).number;
        const builder: Range<Decoration>[] = [];
        for (let i = 1; i <= endLine; i++) {
          builder.push(executedLineDeco.range(doc.line(i).from));
        }
        return Decoration.set(builder);
      }
    }
    // Clear decorations when document is edited to avoid misaligned highlights
    if (tr.docChanged) {
      return Decoration.none;
    }
    return decos;
  },
  provide: (f) => EditorView.decorations.from(f),
});

const executedTheme = EditorView.baseTheme({
  '.cm-executed-line': {
    backgroundColor: 'rgba(34, 197, 94, 0.1)',
  },
  '&dark .cm-executed-line': {
    backgroundColor: 'rgba(34, 197, 94, 0.15)',
  },
});

// Compartments are created per-instance via useRef to avoid sharing across multiple editors

interface CoqEditorProps {
  value: string;
  onChange: (value: string) => void;
  onExecuteNext?: () => void;
  onExecutePrev?: () => void;
  onExecuteAll?: () => void;
  onExecuteToPosition?: (charOffset: number) => void;
  onCursorActivity?: (offset: number) => void;
  executedUpTo?: number;
  readOnly?: boolean;
  className?: string;
}

export function CoqEditor({
  value,
  onChange,
  onExecuteNext,
  onExecutePrev,
  onExecuteAll,
  onExecuteToPosition,
  onCursorActivity,
  executedUpTo = 0,
  readOnly = false,
  className = '',
}: CoqEditorProps) {
  const containerRef = useRef<HTMLDivElement>(null);
  const viewRef = useRef<EditorView | null>(null);
  const themeCompartmentRef = useRef(new Compartment());
  const readOnlyCompartmentRef = useRef(new Compartment());
  const onChangeRef = useRef(onChange);
  const onExecuteNextRef = useRef(onExecuteNext);
  const onExecutePrevRef = useRef(onExecutePrev);
  const onExecuteAllRef = useRef(onExecuteAll);
  const onExecuteToPositionRef = useRef(onExecuteToPosition);
  const onCursorActivityRef = useRef(onCursorActivity);

  // Get theme from next-themes
  const { resolvedTheme } = useTheme();
  const [mounted, setMounted] = useState(false);

  // Ensure we're mounted before accessing theme (avoid hydration mismatch)
  useEffect(() => {
    setMounted(true);
  }, []);

  // Determine editor theme based on resolved system theme
  const editorTheme = mounted && resolvedTheme === 'dark' ? 'dark' : 'light';

  // Keep callback refs up to date
  useEffect(() => {
    onChangeRef.current = onChange;
    onExecuteNextRef.current = onExecuteNext;
    onExecutePrevRef.current = onExecutePrev;
    onExecuteAllRef.current = onExecuteAll;
    onExecuteToPositionRef.current = onExecuteToPosition;
    onCursorActivityRef.current = onCursorActivity;
  }, [onChange, onExecuteNext, onExecutePrev, onExecuteAll, onExecuteToPosition, onCursorActivity]);

  // Create custom keybindings for Coq execution
  const coqKeymap = useMemo(() => keymap.of([
    {
      key: 'Alt-n',
      mac: 'Alt-n',
      run: () => {
        onExecuteNextRef.current?.();
        return true;
      },
    },
    {
      key: 'Alt-ArrowDown',
      mac: 'Alt-ArrowDown',
      run: () => {
        onExecuteNextRef.current?.();
        return true;
      },
    },
    {
      key: 'Alt-p',
      mac: 'Alt-p',
      run: () => {
        onExecutePrevRef.current?.();
        return true;
      },
    },
    {
      key: 'Alt-ArrowUp',
      mac: 'Alt-ArrowUp',
      run: () => {
        onExecutePrevRef.current?.();
        return true;
      },
    },
    {
      key: 'Alt-Enter',
      mac: 'Alt-Enter',
      run: () => {
        onExecuteAllRef.current?.();
        return true;
      },
    },
    {
      key: 'Alt-ArrowRight',
      mac: 'Alt-ArrowRight',
      run: () => {
        onExecuteAllRef.current?.();
        return true;
      },
    },
    {
      key: 'Ctrl-Shift-Enter',
      mac: 'Cmd-Shift-Enter',
      run: (view: EditorView) => {
        const offset = view.state.selection.main.head;
        onExecuteToPositionRef.current?.(offset);
        return true;
      },
    },
  ]), []);

  // Initialize editor (only on mount / readOnly change)
  useEffect(() => {
    if (!containerRef.current) return;

    // Destroy existing view first if any
    if (viewRef.current) {
      viewRef.current.destroy();
      viewRef.current = null;
    }

    const extensions = [
      lineNumbers(),
      highlightActiveLine(),
      highlightActiveLineGutter(),
      history(),
      bracketMatching(),
      coqLanguage,
      syntaxHighlighting(defaultHighlightStyle),
      keymap.of([...defaultKeymap, ...historyKeymap]),
      coqKeymap,
      coqAutocomplete,
      coqHoverTooltip,
      executedField,
      executedTheme,
      // Use compartments for dynamic reconfiguration
      themeCompartmentRef.current.of(editorTheme === 'dark' ? oneDark : []),
      readOnlyCompartmentRef.current.of(EditorState.readOnly.of(readOnly)),
      EditorView.updateListener.of((update) => {
        if (update.docChanged) {
          onChangeRef.current(update.state.doc.toString());
        }
        if (update.selectionSet) {
          onCursorActivityRef.current?.(update.state.selection.main.head);
        }
      }),
      EditorView.lineWrapping,
    ];

    const state = EditorState.create({
      doc: value,
      extensions,
    });

    const view = new EditorView({
      state,
      parent: containerRef.current,
    });

    viewRef.current = view;

    return () => {
      view.destroy();
      if (viewRef.current === view) {
        viewRef.current = null;
      }
    };
  // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [readOnly]);

  // Dynamically switch theme without recreating editor (preserves cursor, undo, scroll)
  useEffect(() => {
    const view = viewRef.current;
    if (!view) return;
    view.dispatch({
      effects: themeCompartmentRef.current.reconfigure(editorTheme === 'dark' ? oneDark : []),
    });
  }, [editorTheme]);

  // Update execution highlighting
  useEffect(() => {
    const view = viewRef.current;
    if (!view) return;
    view.dispatch({ effects: setExecutedUpTo.of(executedUpTo) });
  }, [executedUpTo]);

  // Update content when value changes externally
  useEffect(() => {
    const view = viewRef.current;
    if (!view) return;

    const currentValue = view.state.doc.toString();
    if (currentValue !== value) {
      view.dispatch({
        changes: {
          from: 0,
          to: currentValue.length,
          insert: value,
        },
      });
    }
  }, [value]);

  return (
    <div
      ref={containerRef}
      className={`coq-editor h-full overflow-auto border rounded-md ${className}`}
      style={{
        fontFamily: 'ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, monospace',
        fontSize: '14px',
      }}
    />
  );
}
