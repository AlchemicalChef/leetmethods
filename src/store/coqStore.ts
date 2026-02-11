/**
 * @module coqStore
 *
 * Ephemeral Zustand store for the Coq proof assistant session state.
 *
 * Unlike the other stores in LeetMethods (progressStore, editorStore, etc.),
 * this store is NOT persisted to localStorage. It holds transient data that
 * only makes sense for the current browser session: the jsCoq worker status,
 * the current proof goals, accumulated messages, cursor position tracking,
 * proof lifecycle state, and the guided-mode toggle.
 *
 * This store acts as the React-facing surface for data that originates from
 * the CoqService singleton (which communicates with jsCoq via postMessage IPC
 * through a hidden iframe). Components subscribe to individual slices of this
 * store to re-render when Coq state changes -- for example, GoalsPanel reads
 * `goals`, the editor highlights `errorPosition`, and ProblemSolver checks
 * `proofState` to decide when to show the success banner.
 *
 * Key design decisions:
 * - No persistence: Coq session state is meaningless across page reloads
 *   because the jsCoq iframe is re-initialized from scratch.
 * - Proof state machine: `proofState` uses explicit transitions to prevent
 *   false-positive completions. The `setGoals([])` call that happens during
 *   `verify()`'s internal reset does NOT auto-transition to 'completed' --
 *   only an explicit `setProofState('completed')` does that.
 * - Message cap: Messages are capped at MAX_MESSAGES to prevent unbounded
 *   memory growth during long proof sessions.
 * - guidedMode is intentionally excluded from `reset()` because it is a user
 *   preference that should survive problem switches within a session.
 */

import { create } from 'zustand';
import type { CoqGoal, CoqWorkerStatus, CoqMessage } from '@/lib/coq/types';

/* ─── Re-exports ────────────────────────────────────────────────────────────
 * These re-exports allow consumers to import Coq types directly from the
 * store module without needing a separate import from `@/lib/coq/types`.
 * ──────────────────────────────────────────────────────────────────────── */
export type { CoqGoal, CoqMessage };
export type CoqStatus = CoqWorkerStatus;

/**
 * Represents the lifecycle of a proof attempt.
 *
 * - `'not_started'` -- User has not yet executed any Coq tactics.
 * - `'in_progress'` -- At least one goal has appeared; proof is underway.
 * - `'completed'`   -- All goals have been discharged and the verifier
 *                       confirmed success. Set explicitly by the submission
 *                       handler, never by goal-count transitions alone.
 *
 * Transitions are intentionally conservative to avoid false positives:
 *   not_started -> in_progress:  automatic when goals first appear
 *   in_progress -> completed:    explicit via setProofState('completed')
 *   any         -> not_started:  via reset()
 */
export type ProofState = 'not_started' | 'in_progress' | 'completed';

/**
 * Maximum number of messages retained in the store. Older messages are
 * discarded when this limit is exceeded to prevent memory leaks during
 * long editing sessions where the user runs many Coq commands.
 */
const MAX_MESSAGES = 100;

/* ─── Store Interface ───────────────────────────────────────────────────── */

interface CoqState {
  /** Current status of the jsCoq worker (idle, loading, ready, error, etc.) */
  status: CoqStatus;

  /** Active proof goals returned by jsCoq after the last executed sentence. */
  goals: CoqGoal[];

  /**
   * Rolling log of messages from jsCoq (errors, warnings, informational).
   * Capped at MAX_MESSAGES to bound memory usage.
   */
  messages: CoqMessage[];

  /** Character offset in the editor up to which Coq has successfully executed. */
  currentPosition: number;

  /**
   * Character offset where the most recent Coq error occurred, or null if
   * no error. Used by the editor to highlight the error location.
   */
  errorPosition: number | null;

  /**
   * Explicit proof lifecycle state. See the `ProofState` type documentation
   * for transition rules and the rationale for explicit management.
   */
  proofState: ProofState;

  /**
   * Whether guided mode is enabled. In guided mode, the UI provides
   * step-by-step tactic suggestions. This is a session-level user preference
   * that persists across problem switches (not reset by `reset()`).
   */
  guidedMode: boolean;

  /* ── Actions ──────────────────────────────────────────────────────────── */

  /** Update the jsCoq worker status. */
  setStatus: (status: CoqStatus) => void;

  /**
   * Replace the current goals array and conditionally transition proof state.
   * Auto-transitions from 'not_started' to 'in_progress' when goals appear.
   * Does NOT auto-transition to 'completed' when goals become empty.
   */
  setGoals: (goals: CoqGoal[]) => void;

  /** Explicitly set the proof state. Used to mark 'completed' after successful verification. */
  setProofState: (state: ProofState) => void;

  /**
   * Append a message to the log with the current timestamp.
   * Trims the log to the most recent MAX_MESSAGES entries if it overflows.
   */
  addMessage: (type: CoqMessage['type'], content: string) => void;

  /** Clear the entire message log. */
  clearMessages: () => void;

  /** Update the character offset that Coq has executed up to in the editor. */
  setCurrentPosition: (position: number) => void;

  /** Set or clear the error position in the editor. Pass null to clear. */
  setErrorPosition: (position: number | null) => void;

  /** Toggle guided mode on/off. */
  toggleGuidedMode: () => void;

  /** Explicitly set guided mode to a specific value. */
  setGuidedMode: (enabled: boolean) => void;

  /**
   * Reset all ephemeral Coq state to initial values. Called when navigating
   * away from a problem or starting fresh. Note: `guidedMode` is intentionally
   * preserved because it is a user preference, not session state.
   */
  reset: () => void;
}

/* ─── Store Creation ────────────────────────────────────────────────────── */

export const useCoqStore = create<CoqState>((set) => ({
  status: 'idle',
  goals: [],
  messages: [],
  currentPosition: 0,
  errorPosition: null,
  proofState: 'not_started',
  guidedMode: false,

  setStatus: (status: CoqStatus) => set({ status }),

  setGoals: (goals: CoqGoal[]) => {
    set((state) => {
      let newProofState = state.proofState;

      /**
       * Only auto-transition from 'not_started' to 'in_progress' when goals
       * first appear. This indicates the user has started executing tactics.
       *
       * Crucially, we do NOT auto-transition to 'completed' when goals become
       * empty (goals.length === 0), because that also happens during internal
       * resets (e.g., when the verifier calls reset before re-executing).
       * Completion is set explicitly by the submission handler after the
       * verifier confirms all obligations are discharged.
       */
      if (goals.length > 0 && state.proofState === 'not_started') {
        newProofState = 'in_progress';
      }
      return { goals, proofState: newProofState };
    });
  },

  setProofState: (proofState: ProofState) => set({ proofState }),

  addMessage: (type: CoqMessage['type'], content: string) =>
    set((state) => {
      const newMessage = { type, content, timestamp: Date.now() };
      const messages = [...state.messages, newMessage];

      /**
       * Enforce the message cap by keeping only the most recent MAX_MESSAGES.
       * This prevents memory leaks during long sessions where the user
       * repeatedly executes and undoes tactics, each generating messages.
       */
      if (messages.length > MAX_MESSAGES) {
        return { messages: messages.slice(-MAX_MESSAGES) };
      }
      return { messages };
    }),

  clearMessages: () => set({ messages: [] }),

  setCurrentPosition: (position: number) => set({ currentPosition: position }),

  setErrorPosition: (position: number | null) => set({ errorPosition: position }),

  toggleGuidedMode: () => set((state) => ({ guidedMode: !state.guidedMode })),
  setGuidedMode: (enabled: boolean) => set({ guidedMode: enabled }),

  reset: () =>
    set({
      status: 'idle',
      goals: [],
      messages: [],
      currentPosition: 0,
      errorPosition: null,
      proofState: 'not_started',
      /**
       * guidedMode is intentionally NOT reset here. It is a user preference
       * that should persist across problem navigations within the same session.
       * The user toggles it once and expects it to stay until they toggle again.
       */
    }),
}));
