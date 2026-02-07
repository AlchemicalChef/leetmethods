import { describe, it, expect, beforeEach, vi } from 'vitest';
import { useCoqStore } from './coqStore';
import type { CoqGoal } from '@/lib/coq/types';

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

const goal = (id: number, conclusion: string): CoqGoal => ({
  id,
  hypotheses: [],
  conclusion,
});

function resetStore() {
  useCoqStore.getState().reset();
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('coqStore', () => {
  beforeEach(() => {
    resetStore();
  });

  // -- Initial state --------------------------------------------------------

  it('has correct initial state', () => {
    const state = useCoqStore.getState();
    expect(state.status).toBe('idle');
    expect(state.goals).toEqual([]);
    expect(state.messages).toEqual([]);
    expect(state.currentPosition).toBe(0);
    expect(state.errorPosition).toBeNull();
    expect(state.proofState).toBe('not_started');
  });

  // -- setStatus ------------------------------------------------------------

  it('updates status', () => {
    useCoqStore.getState().setStatus('ready');
    expect(useCoqStore.getState().status).toBe('ready');
  });

  // -- setGoals: proof state transitions ------------------------------------

  it('auto-transitions proofState from not_started to in_progress when goals appear', () => {
    expect(useCoqStore.getState().proofState).toBe('not_started');
    useCoqStore.getState().setGoals([goal(1, 'True')]);
    expect(useCoqStore.getState().proofState).toBe('in_progress');
    expect(useCoqStore.getState().goals).toHaveLength(1);
  });

  it('does not transition proofState when goals are empty', () => {
    useCoqStore.getState().setGoals([]);
    expect(useCoqStore.getState().proofState).toBe('not_started');
  });

  it('stays in_progress when new goals are set while already in_progress', () => {
    useCoqStore.getState().setGoals([goal(1, 'True')]); // not_started → in_progress
    useCoqStore.getState().setGoals([goal(2, 'False')]); // stays in_progress
    expect(useCoqStore.getState().proofState).toBe('in_progress');
    expect(useCoqStore.getState().goals).toEqual([goal(2, 'False')]);
  });

  it('does not auto-transition back from completed when goals appear', () => {
    useCoqStore.getState().setProofState('completed');
    useCoqStore.getState().setGoals([goal(1, 'True')]);
    expect(useCoqStore.getState().proofState).toBe('completed');
  });

  it('does not auto-transition from in_progress to in_progress on empty goals', () => {
    useCoqStore.getState().setGoals([goal(1, 'True')]); // → in_progress
    useCoqStore.getState().setGoals([]); // stays in_progress
    expect(useCoqStore.getState().proofState).toBe('in_progress');
  });

  // -- setProofState --------------------------------------------------------

  it('allows explicit proof state transitions', () => {
    useCoqStore.getState().setProofState('completed');
    expect(useCoqStore.getState().proofState).toBe('completed');
    useCoqStore.getState().setProofState('not_started');
    expect(useCoqStore.getState().proofState).toBe('not_started');
  });

  // -- addMessage -----------------------------------------------------------

  it('adds a message with timestamp', () => {
    vi.useFakeTimers();
    vi.setSystemTime(new Date(2025, 5, 15, 12, 0, 0));

    useCoqStore.getState().addMessage('info', 'Hello');

    const messages = useCoqStore.getState().messages;
    expect(messages).toHaveLength(1);
    expect(messages[0].type).toBe('info');
    expect(messages[0].content).toBe('Hello');
    expect(messages[0].timestamp).toBe(Date.now());

    vi.useRealTimers();
  });

  it('appends messages in order', () => {
    useCoqStore.getState().addMessage('info', 'first');
    useCoqStore.getState().addMessage('error', 'second');
    useCoqStore.getState().addMessage('warning', 'third');

    const messages = useCoqStore.getState().messages;
    expect(messages).toHaveLength(3);
    expect(messages[0].content).toBe('first');
    expect(messages[1].content).toBe('second');
    expect(messages[2].content).toBe('third');
  });

  it('truncates messages to MAX_MESSAGES (100) keeping the most recent', () => {
    // Add 105 messages
    for (let i = 0; i < 105; i++) {
      useCoqStore.getState().addMessage('info', `msg-${i}`);
    }

    const messages = useCoqStore.getState().messages;
    expect(messages).toHaveLength(100);
    // Should keep messages 5-104 (the last 100)
    expect(messages[0].content).toBe('msg-5');
    expect(messages[99].content).toBe('msg-104');
  });

  it('does not truncate when at exactly MAX_MESSAGES', () => {
    for (let i = 0; i < 100; i++) {
      useCoqStore.getState().addMessage('info', `msg-${i}`);
    }
    expect(useCoqStore.getState().messages).toHaveLength(100);
  });

  // -- clearMessages --------------------------------------------------------

  it('clears all messages', () => {
    useCoqStore.getState().addMessage('info', 'one');
    useCoqStore.getState().addMessage('error', 'two');
    useCoqStore.getState().clearMessages();
    expect(useCoqStore.getState().messages).toEqual([]);
  });

  // -- position -------------------------------------------------------------

  it('sets current position', () => {
    useCoqStore.getState().setCurrentPosition(42);
    expect(useCoqStore.getState().currentPosition).toBe(42);
  });

  it('sets and clears error position', () => {
    useCoqStore.getState().setErrorPosition(10);
    expect(useCoqStore.getState().errorPosition).toBe(10);
    useCoqStore.getState().setErrorPosition(null);
    expect(useCoqStore.getState().errorPosition).toBeNull();
  });

  // -- reset ----------------------------------------------------------------

  it('resets all state to initial values', () => {
    // Mutate everything
    useCoqStore.getState().setStatus('busy');
    useCoqStore.getState().setGoals([goal(1, 'True')]);
    useCoqStore.getState().addMessage('error', 'fail');
    useCoqStore.getState().setCurrentPosition(50);
    useCoqStore.getState().setErrorPosition(25);
    useCoqStore.getState().setProofState('completed');

    useCoqStore.getState().reset();

    const state = useCoqStore.getState();
    expect(state.status).toBe('idle');
    expect(state.goals).toEqual([]);
    expect(state.messages).toEqual([]);
    expect(state.currentPosition).toBe(0);
    expect(state.errorPosition).toBeNull();
    expect(state.proofState).toBe('not_started');
  });
});

// ---------------------------------------------------------------------------
// proofState direct checks
// ---------------------------------------------------------------------------

describe('proofState values', () => {
  beforeEach(() => {
    useCoqStore.getState().reset();
  });

  it('is completed after setProofState("completed")', () => {
    useCoqStore.getState().setProofState('completed');
    expect(useCoqStore.getState().proofState).toBe('completed');
  });

  it('is not_started initially', () => {
    expect(useCoqStore.getState().proofState).toBe('not_started');
  });

  it('is in_progress after setProofState("in_progress")', () => {
    useCoqStore.getState().setProofState('in_progress');
    expect(useCoqStore.getState().proofState).toBe('in_progress');
  });
});
