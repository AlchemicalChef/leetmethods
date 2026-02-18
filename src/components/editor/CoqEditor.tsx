/**
 * @module CoqEditor
 *
 * A CodeMirror 6-based editor component specialized for writing Coq proofs.
 *
 * This component is the primary code editing surface in LeetMethods. It wraps
 * CodeMirror 6 with Coq-specific extensions including:
 * - Custom Coq syntax highlighting (via `coq-syntax.ts`)
 * - Coq tactic autocompletion (via `coq-autocomplete.ts`)
 * - Hover tooltips for tactic documentation (via `coq-hover.ts`)
 * - Execution highlighting that visually marks lines already sent to jsCoq
 * - Custom keybindings for step-forward, step-back, and execute-all
 *
 * Key design decisions:
 * - Uses CodeMirror Compartments for dynamic theme and readOnly reconfiguration
 *   so that toggling dark mode or readOnly does not destroy the editor instance
 *   (which would lose undo history, cursor position, and scroll state).
 * - Callback refs (useRef) are used for all event handlers to avoid recreating
 *   the editor when callbacks change. The editor is only recreated when `readOnly`
 *   changes, since that fundamentally alters the extension set.
 * - External value changes are diffed against the current document to avoid
 *   unnecessary dispatches (which would reset selection/undo).
 * - The execution highlight state field clears decorations on any document edit
 *   to prevent stale green highlights from misaligning after user edits.
 *
 * @see {@link CoqService} for the jsCoq iframe bridge that executes Coq code
 * @see {@link ProblemSolver} for the parent component that orchestrates the editor
 */
'use client';

import { useEffect, useRef, useMemo, useState } from 'react';
import { EditorState, StateEffect, StateField, Compartment, type Range } from '@codemirror/state';
import { EditorView, Decoration, keymap, lineNumbers, highlightActiveLine, highlightActiveLineGutter } from '@codemirror/view';
import { defaultKeymap, history, historyKeymap } from '@codemirror/commands';
import { syntaxHighlighting, defaultHighlightStyle, bracketMatching } from '@codemirror/language';
import { oneDark } from '@codemirror/theme-one-dark';
import { useTheme } from 'next-themes';
import { coqLanguage } from '@/lib/coq/coq-syntax';
import { setDiagnostics } from '@codemirror/lint';
import type { Diagnostic } from '@codemirror/lint';
import { coqAutocomplete, setEditorGoals } from '@/lib/coq/coq-autocomplete';
import { coqHoverTooltip } from '@/lib/coq/coq-hover';
import { coqFolding } from '@/lib/coq/coq-folding';
import { coqLinter } from '@/lib/coq/coq-linter';
import { coqSignatureHelp } from '@/lib/coq/coq-signature';
import { coqCommentClose } from '@/lib/coq/coq-closebracket';
import type { CoqGoal } from '@/lib/coq/types';
import type { CoqDiagnostic } from '@/lib/coq/coq-diagnostics';

/* ============================================================================
 * Execution Highlight System
 *
 * When the user executes Coq statements step-by-step, lines that have been
 * successfully processed by jsCoq are highlighted with a green background.
 * This is implemented as a CodeMirror StateField + StateEffect pair:
 *
 * 1. `setExecutedUpTo` effect carries a character offset (the end of the last
 *    executed statement).
 * 2. `executedField` rebuilds line decorations from line 1 up to the line
 *    containing that offset.
 * 3. On any document change, decorations are cleared because character offsets
 *    from the Coq state machine no longer correspond to document positions.
 * ============================================================================ */

/**
 * StateEffect that sets the character offset up to which lines should be
 * highlighted as "executed." A value of 0 or less clears all highlights.
 */
const setExecutedUpTo = StateEffect.define<number>();

/**
 * Line decoration applied to each executed line -- a subtle green background.
 */
const executedLineDeco = Decoration.line({ class: 'cm-executed-line' });

/**
 * StateField that tracks which lines are decorated as "executed."
 *
 * Behavior:
 * - When a `setExecutedUpTo` effect is received, rebuilds decorations from
 *   line 1 through the line containing the offset.
 * - When the document changes (user typing), clears all decorations to avoid
 *   misaligned highlights -- the Coq execution state is invalidated on edit.
 * - Otherwise preserves the existing decoration set unchanged.
 */
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
        // Clamp offset to document length to handle edge cases where
        // the Coq state reports an offset beyond the current document
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

/**
 * Base theme for executed line highlighting.
 * Uses semi-transparent green with slightly higher opacity in dark mode
 * for better visibility against dark backgrounds.
 */
const executedTheme = EditorView.baseTheme({
  '.cm-executed-line': {
    backgroundColor: 'rgba(34, 197, 94, 0.1)',
  },
  '&dark .cm-executed-line': {
    backgroundColor: 'rgba(34, 197, 94, 0.15)',
  },
});

/* ============================================================================
 * CoqEditor Component
 * ============================================================================ */

/**
 * Props for the CoqEditor component.
 *
 * The editor operates as a controlled component: `value` is the source of truth
 * and `onChange` fires when the user edits. Execution callbacks are optional
 * because some contexts (e.g., tutorial read-only views) do not need them.
 */
interface CoqEditorProps {
  /** Current editor content (controlled) */
  value: string;
  /** Called when user edits the document */
  onChange: (value: string) => void;
  /** Execute next Coq statement (step forward) */
  onExecuteNext?: () => void;
  /** Undo last executed Coq statement (step back) */
  onExecutePrev?: () => void;
  /** Execute all remaining statements */
  onExecuteAll?: () => void;
  /** Execute statements up to a specific character offset (execute-to-cursor) */
  onExecuteToPosition?: (charOffset: number) => void;
  /** Called when the cursor position changes, reporting the character offset */
  onCursorActivity?: (offset: number) => void;
  /** Current proof goals — used for hypothesis-aware autocomplete */
  goals?: CoqGoal[];
  /** Inline error diagnostic to display as a red squiggly underline */
  diagnostics?: CoqDiagnostic | null;
  /** Ref that CoqEditor populates with an insert-at-cursor function */
  insertTextRef?: React.MutableRefObject<((text: string) => void) | null>;
  /** Character offset up to which lines should be highlighted green */
  executedUpTo?: number;
  /** Whether the editor is read-only (used in tutorial/solution views) */
  readOnly?: boolean;
  /** Additional CSS classes for the container div */
  className?: string;
}

/**
 * CodeMirror 6 editor configured for Coq proof editing.
 *
 * Integrates Coq syntax highlighting, autocompletion, hover tooltips,
 * execution highlighting, and keyboard shortcuts for interacting with
 * the jsCoq proof assistant.
 *
 * @param props - See {@link CoqEditorProps}
 * @returns A div element that mounts the CodeMirror editor
 */
export function CoqEditor({
  value,
  onChange,
  onExecuteNext,
  onExecutePrev,
  onExecuteAll,
  onExecuteToPosition,
  onCursorActivity,
  goals = [],
  diagnostics = null,
  insertTextRef,
  executedUpTo = 0,
  readOnly = false,
  className = '',
}: CoqEditorProps) {
  /** DOM container where CodeMirror mounts its view */
  const containerRef = useRef<HTMLDivElement>(null);
  /** Reference to the active CodeMirror EditorView instance */
  const viewRef = useRef<EditorView | null>(null);

  /**
   * Compartments enable dynamic reconfiguration of specific extensions
   * without recreating the entire editor. Each is created per-instance
   * via useRef to prevent sharing state across multiple CoqEditor instances.
   */
  const themeCompartmentRef = useRef(new Compartment());
  const readOnlyCompartmentRef = useRef(new Compartment());

  /**
   * Callback refs allow the CodeMirror update listener (created once at mount)
   * to always call the latest callback without triggering editor recreation.
   * This pattern avoids stale closures in the long-lived CodeMirror instance.
   */
  const onChangeRef = useRef(onChange);
  const onExecuteNextRef = useRef(onExecuteNext);
  const onExecutePrevRef = useRef(onExecutePrev);
  const onExecuteAllRef = useRef(onExecuteAll);
  const onExecuteToPositionRef = useRef(onExecuteToPosition);
  const onCursorActivityRef = useRef(onCursorActivity);

  /** Resolve the active theme from next-themes (system/light/dark) */
  const { resolvedTheme } = useTheme();
  const [mounted, setMounted] = useState(false);

  /**
   * Track mount state to avoid hydration mismatches. During SSR,
   * `resolvedTheme` is undefined, so we default to light theme
   * until the component mounts on the client.
   */
  useEffect(() => {
    setMounted(true);
  }, []);

  /** Determine which CodeMirror theme to use based on the resolved system theme */
  const editorTheme = mounted && resolvedTheme === 'dark' ? 'dark' : 'light';

  /** Keep callback refs in sync with the latest prop values */
  useEffect(() => {
    onChangeRef.current = onChange;
    onExecuteNextRef.current = onExecuteNext;
    onExecutePrevRef.current = onExecutePrev;
    onExecuteAllRef.current = onExecuteAll;
    onExecuteToPositionRef.current = onExecuteToPosition;
    onCursorActivityRef.current = onCursorActivity;
  }, [onChange, onExecuteNext, onExecutePrev, onExecuteAll, onExecuteToPosition, onCursorActivity]);

  /**
   * Custom Coq execution keybindings.
   *
   * Memoized once since they reference stable refs, not changing callbacks.
   * All shortcuts use Alt as the modifier to avoid conflicts with standard
   * editor shortcuts (Ctrl/Cmd). Two bindings per action provide both
   * letter-based (Alt+N/P) and arrow-based (Alt+Down/Up) alternatives.
   */
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
        // Use the current cursor position as the target offset
        const offset = view.state.selection.main.head;
        onExecuteToPositionRef.current?.(offset);
        return true;
      },
    },
  ]), []);

  /**
   * Initialize the CodeMirror editor.
   *
   * This effect runs on mount and when `readOnly` changes. We intentionally
   * omit `value` and `editorTheme` from the dependency array because:
   * - `value` changes are handled by a separate sync effect below
   * - `editorTheme` changes use the compartment reconfigure mechanism
   *
   * Recreating the editor on readOnly change is necessary because some
   * extensions behave differently in read-only mode.
   */
  useEffect(() => {
    if (!containerRef.current) return;

    // Destroy existing view first if any (handles readOnly toggle)
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
      coqFolding,
      coqLinter,
      coqSignatureHelp,
      coqCommentClose,
      executedField,
      executedTheme,
      // Compartments allow theme and readOnly to be reconfigured dynamically
      themeCompartmentRef.current.of(editorTheme === 'dark' ? oneDark : []),
      readOnlyCompartmentRef.current.of(EditorState.readOnly.of(readOnly)),
      // Single update listener handles both document changes and cursor movement
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
      // Only null out the ref if it still points to this view
      // (guards against race conditions with React Strict Mode double-mount)
      if (viewRef.current === view) {
        viewRef.current = null;
      }
    };
  // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [readOnly]);

  /**
   * Populate the insertTextRef with a function that inserts text at the
   * current cursor position. Used by GoalsPanel's click-to-insert feature.
   */
  useEffect(() => {
    if (!insertTextRef) return;
    insertTextRef.current = (text: string) => {
      const view = viewRef.current;
      if (!view) return;
      const cursor = view.state.selection.main.head;
      view.dispatch({
        changes: { from: cursor, insert: text },
        selection: { anchor: cursor + text.length },
      });
      view.focus();
    };
    return () => {
      if (insertTextRef) insertTextRef.current = null;
    };
  }, [insertTextRef]);

  /**
   * Dynamically switch the editor theme without recreating the editor.
   * This preserves cursor position, undo history, and scroll position
   * when the user toggles between light and dark mode.
   */
  useEffect(() => {
    const view = viewRef.current;
    if (!view) return;
    view.dispatch({
      effects: themeCompartmentRef.current.reconfigure(editorTheme === 'dark' ? oneDark : []),
    });
  }, [editorTheme]);

  /**
   * Update the execution highlight decoration whenever the parent
   * reports a new `executedUpTo` offset (after step-forward/back).
   */
  useEffect(() => {
    const view = viewRef.current;
    if (!view) return;
    view.dispatch({ effects: setExecutedUpTo.of(executedUpTo) });
  }, [executedUpTo]);

  /**
   * Update the goals StateField for context-aware autocomplete.
   * Hypothesis names from the current proof context appear as completions.
   */
  useEffect(() => {
    const view = viewRef.current;
    if (!view) return;
    view.dispatch({ effects: setEditorGoals.of(goals) });
  }, [goals]);

  /**
   * Update inline diagnostics (red squiggly underlines) when the
   * parent reports a Coq error or clears it.
   */
  useEffect(() => {
    const view = viewRef.current;
    if (!view) return;
    if (diagnostics) {
      const docLen = view.state.doc.length;
      const from = Math.min(diagnostics.from, docLen);
      const to = Math.min(diagnostics.to, docLen);
      if (from < to) {
        const cm6Diags: Diagnostic[] = [{
          from,
          to,
          message: diagnostics.message,
          severity: diagnostics.severity,
        }];
        view.dispatch(setDiagnostics(view.state, cm6Diags));
      } else {
        view.dispatch(setDiagnostics(view.state, []));
      }
    } else {
      view.dispatch(setDiagnostics(view.state, []));
    }
  }, [diagnostics]);

  /**
   * Sync external value changes into the editor.
   *
   * This handles the case where the parent resets the code (e.g., problem
   * change or reset button). We compare against the current document to
   * avoid dispatching a no-op change, which would clear undo history.
   */
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
