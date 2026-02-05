import { create } from 'zustand';
import type { CoqGoal, CoqWorkerStatus } from '@/lib/coq/types';

export type { CoqGoal };
export type CoqStatus = CoqWorkerStatus;

export interface CoqMessage {
  type: 'info' | 'error' | 'warning' | 'success' | 'notice';
  content: string;
  timestamp: number;
}

// FIX #11: Track proof state explicitly
export type ProofState = 'not_started' | 'in_progress' | 'completed';

// FIX #7: Limit message history
const MAX_MESSAGES = 100;

interface CoqState {
  status: CoqStatus;
  goals: CoqGoal[];
  messages: CoqMessage[];
  currentPosition: number;
  errorPosition: number | null;
  proofState: ProofState; // FIX #11: Explicit proof state

  setStatus: (status: CoqStatus) => void;
  setGoals: (goals: CoqGoal[]) => void;
  setProofState: (state: ProofState) => void;
  addMessage: (type: CoqMessage['type'], content: string) => void;
  clearMessages: () => void;
  setCurrentPosition: (position: number) => void;
  setErrorPosition: (position: number | null) => void;
  reset: () => void;
}

export const useCoqStore = create<CoqState>((set) => ({
  status: 'idle',
  goals: [],
  messages: [],
  currentPosition: 0,
  errorPosition: null,
  proofState: 'not_started', // FIX #11: Default to not started

  setStatus: (status: CoqStatus) => set({ status }),

  // FIX #11: Don't automatically set proof complete based on goals alone
  setGoals: (goals: CoqGoal[]) => {
    set((state) => {
      // Only mark as completed if we were in_progress and now have no goals
      let newProofState = state.proofState;
      if (state.proofState === 'in_progress' && goals.length === 0) {
        newProofState = 'completed';
      } else if (goals.length > 0 && state.proofState === 'not_started') {
        newProofState = 'in_progress';
      }
      return { goals, proofState: newProofState };
    });
  },

  setProofState: (proofState: ProofState) => set({ proofState }),

  // FIX #7: Limit messages to prevent memory leak
  addMessage: (type: CoqMessage['type'], content: string) =>
    set((state) => {
      const newMessage = { type, content, timestamp: Date.now() };
      const messages = [...state.messages, newMessage];
      // Keep only the last MAX_MESSAGES
      if (messages.length > MAX_MESSAGES) {
        return { messages: messages.slice(-MAX_MESSAGES) };
      }
      return { messages };
    }),

  clearMessages: () => set({ messages: [] }),

  setCurrentPosition: (position: number) => set({ currentPosition: position }),

  setErrorPosition: (position: number | null) => set({ errorPosition: position }),

  reset: () =>
    set({
      status: 'idle',
      goals: [],
      messages: [],
      currentPosition: 0,
      errorPosition: null,
      proofState: 'not_started', // FIX #11: Reset proof state
    }),
}));

// Helper to check if proof is complete (for backward compatibility)
export const isProofComplete = (state: CoqState): boolean => {
  return state.proofState === 'completed';
};
