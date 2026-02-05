export interface CoqGoal {
  id: number;
  hypotheses: CoqHypothesis[];
  conclusion: string;
}

export interface CoqHypothesis {
  name: string;
  type: string;
}

// FIX #9: Unified CoqMessage type - include 'success' for consistency with store
export interface CoqMessage {
  type: 'info' | 'error' | 'warning' | 'notice' | 'success';
  content: string;
}

export interface VerificationResult {
  success: boolean;
  goals: CoqGoal[];
  errors: string[];
  messages: CoqMessage[];
  hasForbiddenTactics: boolean;
  forbiddenTacticsFound: string[];
  isComplete: boolean; // Qed successful with no remaining goals
}

export interface CoqDocument {
  prelude: string;
  userCode: string;
}

export type CoqWorkerStatus = 'idle' | 'loading' | 'ready' | 'busy' | 'error';

export interface CoqWorkerMessage {
  type: 'status' | 'goals' | 'message' | 'error' | 'complete' | 'verification';
  payload: unknown;
}

export interface CoqCommand {
  id: string;
  type: 'init' | 'exec' | 'cancel' | 'verify';
  code?: string;
  document?: CoqDocument;
  forbiddenTactics?: string[];
}
