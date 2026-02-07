export interface CoqGoal {
  id: number;
  hypotheses: CoqHypothesis[];
  conclusion: string;
}

export interface CoqHypothesis {
  name: string;
  type: string;
}

// Unified CoqMessage type — canonical definition for both lib and store
export interface CoqMessage {
  type: 'info' | 'error' | 'warning' | 'notice' | 'success';
  content: string;
  timestamp?: number; // Set by coqStore.addMessage; optional in lib context
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

export type CoqWorkerStatus = 'idle' | 'loading' | 'ready' | 'busy' | 'error';
