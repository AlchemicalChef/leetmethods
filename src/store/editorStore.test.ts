import { describe, it, expect, beforeEach } from 'vitest';
import { useEditorStore } from './editorStore';

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function resetStore() {
  useEditorStore.setState({
    code: '',
    problemSlug: null,
    isDirty: false,
    savedCodes: {},
  });
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('editorStore', () => {
  beforeEach(() => {
    resetStore();
  });

  // -- Initial state --------------------------------------------------------

  it('has correct initial state', () => {
    const state = useEditorStore.getState();
    expect(state.code).toBe('');
    expect(state.problemSlug).toBeNull();
    expect(state.isDirty).toBe(false);
    expect(state.savedCodes).toEqual({});
  });

  // -- setCode --------------------------------------------------------------

  it('updates code and sets isDirty to true', () => {
    useEditorStore.getState().setCode('intros.');
    const state = useEditorStore.getState();
    expect(state.code).toBe('intros.');
    expect(state.isDirty).toBe(true);
  });

  it('marks isDirty on every setCode call', () => {
    useEditorStore.getState().setCode('a');
    // Manually clear dirty to verify next setCode re-sets it
    useEditorStore.setState({ isDirty: false });
    useEditorStore.getState().setCode('b');
    expect(useEditorStore.getState().isDirty).toBe(true);
  });

  // -- setProblemSlug -------------------------------------------------------

  it('sets the current problem slug', () => {
    useEditorStore.getState().setProblemSlug('modus-ponens');
    expect(useEditorStore.getState().problemSlug).toBe('modus-ponens');
  });

  it('can set problem slug to null', () => {
    useEditorStore.getState().setProblemSlug('modus-ponens');
    useEditorStore.getState().setProblemSlug(null);
    expect(useEditorStore.getState().problemSlug).toBeNull();
  });

  // -- saveCode -------------------------------------------------------------

  it('saves code for the current problem slug and clears isDirty', () => {
    useEditorStore.getState().setProblemSlug('modus-ponens');
    useEditorStore.getState().setCode('Proof. auto. Qed.');
    expect(useEditorStore.getState().isDirty).toBe(true);

    useEditorStore.getState().saveCode();

    const state = useEditorStore.getState();
    expect(state.savedCodes['modus-ponens']).toBe('Proof. auto. Qed.');
    expect(state.isDirty).toBe(false);
  });

  it('does nothing when problemSlug is null', () => {
    useEditorStore.getState().setCode('some code');
    useEditorStore.getState().saveCode(); // no slug set

    const state = useEditorStore.getState();
    expect(state.savedCodes).toEqual({});
    expect(state.isDirty).toBe(true); // still dirty
  });

  it('overwrites previously saved code for the same slug', () => {
    useEditorStore.getState().setProblemSlug('p1');
    useEditorStore.getState().setCode('version 1');
    useEditorStore.getState().saveCode();

    useEditorStore.getState().setCode('version 2');
    useEditorStore.getState().saveCode();

    expect(useEditorStore.getState().savedCodes['p1']).toBe('version 2');
  });

  it('preserves saved codes for other slugs when saving', () => {
    useEditorStore.getState().setProblemSlug('p1');
    useEditorStore.getState().setCode('code-1');
    useEditorStore.getState().saveCode();

    useEditorStore.getState().setProblemSlug('p2');
    useEditorStore.getState().setCode('code-2');
    useEditorStore.getState().saveCode();

    const saved = useEditorStore.getState().savedCodes;
    expect(saved['p1']).toBe('code-1');
    expect(saved['p2']).toBe('code-2');
  });

  // -- loadCode -------------------------------------------------------------

  it('returns saved code when it exists and sets state', () => {
    // Pre-populate saved code
    useEditorStore.setState({
      savedCodes: { 'modus-ponens': 'Proof. exact I. Qed.' },
    });

    const code = useEditorStore.getState().loadCode('modus-ponens', 'default template');

    expect(code).toBe('Proof. exact I. Qed.');
    const state = useEditorStore.getState();
    expect(state.code).toBe('Proof. exact I. Qed.');
    expect(state.problemSlug).toBe('modus-ponens');
    expect(state.isDirty).toBe(false);
  });

  it('returns default code when no saved code exists', () => {
    const code = useEditorStore.getState().loadCode('new-problem', 'default template');

    expect(code).toBe('default template');
    const state = useEditorStore.getState();
    expect(state.code).toBe('default template');
    expect(state.problemSlug).toBe('new-problem');
    expect(state.isDirty).toBe(false);
  });

  it('clears isDirty when loading code', () => {
    useEditorStore.getState().setCode('dirty code');
    expect(useEditorStore.getState().isDirty).toBe(true);

    useEditorStore.getState().loadCode('p1', 'clean');
    expect(useEditorStore.getState().isDirty).toBe(false);
  });

  // -- resetCode ------------------------------------------------------------

  it('resets code to default and removes saved code for current slug', () => {
    useEditorStore.getState().setProblemSlug('p1');
    useEditorStore.getState().setCode('user code');
    useEditorStore.getState().saveCode();
    expect(useEditorStore.getState().savedCodes['p1']).toBe('user code');

    useEditorStore.getState().resetCode('default template');

    const state = useEditorStore.getState();
    expect(state.code).toBe('default template');
    expect(state.savedCodes['p1']).toBeUndefined();
    expect(state.isDirty).toBe(false);
  });

  it('does nothing when problemSlug is null', () => {
    useEditorStore.setState({
      code: 'something',
      savedCodes: { p1: 'saved' },
    });

    useEditorStore.getState().resetCode('default');

    // Nothing should change since problemSlug is null
    const state = useEditorStore.getState();
    expect(state.code).toBe('something');
    expect(state.savedCodes['p1']).toBe('saved');
  });

  it('preserves saved codes for other slugs when resetting', () => {
    useEditorStore.setState({
      problemSlug: 'p1',
      savedCodes: { p1: 'code-1', p2: 'code-2' },
    });

    useEditorStore.getState().resetCode('default');

    const saved = useEditorStore.getState().savedCodes;
    expect(saved['p1']).toBeUndefined();
    expect(saved['p2']).toBe('code-2');
  });

  // -- Full workflow --------------------------------------------------------

  it('supports a complete save-load-reset workflow', () => {
    // Load a problem with default template
    const initial = useEditorStore.getState().loadCode('p1', 'template');
    expect(initial).toBe('template');

    // User edits code
    useEditorStore.getState().setCode('Proof. auto. Qed.');
    expect(useEditorStore.getState().isDirty).toBe(true);

    // Save
    useEditorStore.getState().saveCode();
    expect(useEditorStore.getState().isDirty).toBe(false);

    // Switch to another problem
    const p2Code = useEditorStore.getState().loadCode('p2', 'template-2');
    expect(p2Code).toBe('template-2');

    // Come back to p1 — should load saved code
    const p1Code = useEditorStore.getState().loadCode('p1', 'template');
    expect(p1Code).toBe('Proof. auto. Qed.');

    // Reset p1 — should go back to template
    useEditorStore.getState().resetCode('template');
    expect(useEditorStore.getState().code).toBe('template');

    // Loading p1 again should get template (saved code was deleted)
    const p1Again = useEditorStore.getState().loadCode('p1', 'template');
    expect(p1Again).toBe('template');
  });
});
