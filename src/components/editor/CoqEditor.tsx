'use client';

import { useEffect, useRef, useMemo, useState } from 'react';
import { EditorState } from '@codemirror/state';
import { EditorView, keymap, lineNumbers, highlightActiveLine, highlightActiveLineGutter } from '@codemirror/view';
import { defaultKeymap, history, historyKeymap } from '@codemirror/commands';
import { syntaxHighlighting, defaultHighlightStyle, bracketMatching } from '@codemirror/language';
import { oneDark } from '@codemirror/theme-one-dark';
import { useTheme } from 'next-themes';
import { coqLanguage } from '@/lib/coq/coq-syntax';

interface CoqEditorProps {
  value: string;
  onChange: (value: string) => void;
  onExecuteNext?: () => void;
  onExecutePrev?: () => void;
  onExecuteAll?: () => void;
  readOnly?: boolean;
  className?: string;
}

export function CoqEditor({
  value,
  onChange,
  onExecuteNext,
  onExecutePrev,
  onExecuteAll,
  readOnly = false,
  className = '',
}: CoqEditorProps) {
  const containerRef = useRef<HTMLDivElement>(null);
  const viewRef = useRef<EditorView | null>(null);
  const onChangeRef = useRef(onChange);
  const onExecuteNextRef = useRef(onExecuteNext);
  const onExecutePrevRef = useRef(onExecutePrev);
  const onExecuteAllRef = useRef(onExecuteAll);

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
  }, [onChange, onExecuteNext, onExecutePrev, onExecuteAll]);

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
  ]), []);

  // Initialize editor
  // FIX #5: Store view in local variable for cleanup to avoid race conditions
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
      EditorView.updateListener.of((update) => {
        if (update.docChanged) {
          onChangeRef.current(update.state.doc.toString());
        }
      }),
      EditorView.lineWrapping,
    ];

    if (editorTheme === 'dark') {
      extensions.push(oneDark);
    }

    if (readOnly) {
      extensions.push(EditorState.readOnly.of(true));
    }

    const state = EditorState.create({
      doc: value,
      extensions,
    });

    const view = new EditorView({
      state,
      parent: containerRef.current,
    });

    viewRef.current = view;

    // FIX #5: Capture view in closure for cleanup
    return () => {
      view.destroy();
      if (viewRef.current === view) {
        viewRef.current = null;
      }
    };
  // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [editorTheme, readOnly, coqKeymap]);

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
