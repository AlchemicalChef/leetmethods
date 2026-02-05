'use client';

import type { CoqGoal, CoqMessage, VerificationResult, CoqWorkerStatus } from './types';
import { checkForbiddenTactics, isProofComplete } from './verifier';

export interface CoqServiceCallbacks {
  onStatusChange?: (status: CoqWorkerStatus) => void;
  onGoalsUpdate?: (goals: CoqGoal[]) => void;
  onMessage?: (message: CoqMessage) => void;
  onError?: (error: string) => void;
  onReady?: () => void;
  onExecutionProgress?: (executed: number, total: number) => void;
}

// Simulated Coq service for development/demo purposes
// In production, this would be replaced with actual jsCoq integration
export class CoqService {
  private status: CoqWorkerStatus = 'idle';
  private callbacks: CoqServiceCallbacks;
  private currentGoals: CoqGoal[] = [];
  private executedStatements: string[] = [];
  private currentCode: string = '';
  private proofStarted: boolean = false;

  constructor(callbacks: CoqServiceCallbacks = {}) {
    this.callbacks = callbacks;
  }

  // FIX #1: Allow updating callbacks after construction
  updateCallbacks(callbacks: CoqServiceCallbacks): void {
    this.callbacks = callbacks;
  }

  async initialize(): Promise<void> {
    this.setStatus('loading');
    // Simulate initialization delay
    await new Promise((resolve) => setTimeout(resolve, 500));
    this.setStatus('ready');
    this.callbacks.onReady?.();
  }

  private setStatus(status: CoqWorkerStatus): void {
    this.status = status;
    this.callbacks.onStatusChange?.(status);
  }

  getStatus(): CoqWorkerStatus {
    return this.status;
  }

  setCode(code: string): void {
    this.currentCode = code;
  }

  getCode(): string {
    return this.currentCode;
  }

  // FIX #6: Handle nested comments with a counter instead of boolean
  private parseStatements(code: string): string[] {
    const statements: string[] = [];
    let current = '';
    let commentDepth = 0; // Use counter for nested comments
    let inString = false;

    for (let i = 0; i < code.length; i++) {
      const char = code[i];
      const next = code[i + 1];

      // Handle comment start - increment depth
      if (char === '(' && next === '*' && !inString) {
        commentDepth++;
        current += char;
        continue;
      }

      // Handle comment end - decrement depth
      if (char === '*' && next === ')' && commentDepth > 0 && !inString) {
        commentDepth--;
        current += char;
        continue;
      }

      // Handle string
      if (char === '"' && commentDepth === 0) {
        inString = !inString;
      }

      current += char;

      // Statement terminator (only when not in comment or string)
      if (char === '.' && commentDepth === 0 && !inString) {
        const trimmed = current.trim();
        if (trimmed) {
          statements.push(trimmed);
        }
        current = '';
      }
    }

    return statements;
  }

  // Simulate proof execution
  async executeNext(): Promise<void> {
    if (this.status !== 'ready') {
      throw new Error('Coq is not ready');
    }

    this.setStatus('busy');
    await new Promise((resolve) => setTimeout(resolve, 100));

    const statements = this.parseStatements(this.currentCode);
    const nextIndex = this.executedStatements.length;

    if (nextIndex < statements.length) {
      const statement = statements[nextIndex];
      this.executedStatements.push(statement);
      this.updateGoalsForStatement(statement);
    }

    this.setStatus('ready');
  }

  async executePrev(): Promise<void> {
    if (this.status !== 'ready') {
      throw new Error('Coq is not ready');
    }

    this.setStatus('busy');
    await new Promise((resolve) => setTimeout(resolve, 50));

    if (this.executedStatements.length > 0) {
      this.executedStatements.pop();
      this.recalculateGoals();
    }

    this.setStatus('ready');
  }

  async executeAll(): Promise<void> {
    if (this.status !== 'ready') {
      throw new Error('Coq is not ready');
    }

    this.setStatus('busy');
    const statements = this.parseStatements(this.currentCode);

    for (let i = this.executedStatements.length; i < statements.length; i++) {
      await new Promise((resolve) => setTimeout(resolve, 50));
      this.executedStatements.push(statements[i]);
      this.updateGoalsForStatement(statements[i]);
      this.callbacks.onExecutionProgress?.(i + 1, statements.length);
    }

    this.setStatus('ready');
  }

  async reset(): Promise<void> {
    this.setStatus('busy');
    await new Promise((resolve) => setTimeout(resolve, 50));
    this.executedStatements = [];
    this.currentGoals = [];
    this.proofStarted = false;
    this.callbacks.onGoalsUpdate?.([]);
    this.setStatus('ready');
  }

  isProofStarted(): boolean {
    return this.proofStarted;
  }

  private updateGoalsForStatement(statement: string): void {
    const stmt = statement.toLowerCase().trim();

    // Simulate goal updates based on tactics
    if (stmt.startsWith('proof')) {
      // Starting a proof - show initial goal
      this.proofStarted = true;
      this.simulateInitialGoal();
    } else if (stmt.startsWith('qed')) {
      // Proof complete
      this.currentGoals = [];
      this.proofStarted = false;
      this.callbacks.onMessage?.({ type: 'info', content: 'Proof completed!' });
    } else if (stmt.startsWith('intros')) {
      // Introduce hypotheses
      this.simulateIntros(statement);
    } else if (stmt.startsWith('induction')) {
      // Split into base and inductive cases
      this.simulateInduction();
    } else if (stmt.startsWith('reflexivity') || stmt.startsWith('simpl') || stmt.startsWith('rewrite')) {
      // These tactics might solve the goal or simplify it
      this.simulateTacticProgress();
    } else if (stmt === '-' || stmt === '+' || stmt === '*') {
      // Bullet point - might move to next subgoal
      this.handleBullet();
    }

    this.callbacks.onGoalsUpdate?.(this.currentGoals);
  }

  private simulateInitialGoal(): void {
    // This would be populated based on the theorem being proven
    // For now, create a placeholder
    this.currentGoals = [
      {
        id: 1,
        hypotheses: [],
        conclusion: 'Goal will appear here after executing Proof.',
      },
    ];
  }

  private simulateIntros(statement: string): void {
    // Extract variable names from intros
    const match = statement.match(/intros\s+(.+)/i);
    if (match && this.currentGoals.length > 0) {
      const vars = match[1].split(/\s+/).filter((v) => v !== '.');
      const goal = this.currentGoals[0];
      for (const v of vars) {
        goal.hypotheses.push({ name: v, type: 'unknown' });
      }
    }
  }

  private simulateInduction(): void {
    // Induction creates two subgoals
    if (this.currentGoals.length > 0) {
      const baseGoal: CoqGoal = {
        id: 1,
        hypotheses: [...this.currentGoals[0].hypotheses],
        conclusion: 'Base case goal',
      };
      const inductiveGoal: CoqGoal = {
        id: 2,
        hypotheses: [
          ...this.currentGoals[0].hypotheses,
          { name: 'IHn', type: 'Inductive hypothesis' },
        ],
        conclusion: 'Inductive case goal',
      };
      this.currentGoals = [baseGoal, inductiveGoal];
    }
  }

  private simulateTacticProgress(): void {
    // Remove the first goal (simulating it being solved)
    if (this.currentGoals.length > 0) {
      this.currentGoals = this.currentGoals.slice(1);
    }
  }

  private handleBullet(): void {
    // Bullets focus on subgoals, no state change in simulation
  }

  private recalculateGoals(): void {
    // Re-execute all statements to rebuild goal state
    const savedStatements = [...this.executedStatements];
    this.currentGoals = [];
    this.proofStarted = false;

    for (const stmt of savedStatements) {
      this.updateGoalsForStatement(stmt);
    }
  }

  async verify(
    prelude: string,
    userCode: string,
    forbiddenTactics: string[] = ['admit', 'Admitted']
  ): Promise<VerificationResult> {
    // Check for forbidden tactics
    const { hasForbidden, found } = checkForbiddenTactics(userCode, forbiddenTactics);

    if (hasForbidden) {
      return {
        success: false,
        goals: [],
        errors: [`Forbidden tactics used: ${found.join(', ')}`],
        messages: [{ type: 'error', content: `Forbidden tactics: ${found.join(', ')}` }],
        hasForbiddenTactics: true,
        forbiddenTacticsFound: found,
        isComplete: false,
      };
    }

    // Reset and execute
    await this.reset();
    const fullCode = `${prelude}\n\n${userCode}`;
    this.setCode(fullCode);

    try {
      await this.executeAll();

      const errors: string[] = [];
      const hasQed = isProofComplete(userCode);
      const isComplete = this.currentGoals.length === 0 && hasQed && errors.length === 0;

      return {
        success: isComplete,
        goals: this.currentGoals,
        errors,
        messages: [],
        hasForbiddenTactics: false,
        forbiddenTacticsFound: [],
        isComplete,
      };
    } catch (error) {
      return {
        success: false,
        goals: this.currentGoals,
        errors: [error instanceof Error ? error.message : 'Verification failed'],
        messages: [],
        hasForbiddenTactics: false,
        forbiddenTacticsFound: [],
        isComplete: false,
      };
    }
  }

  destroy(): void {
    this.executedStatements = [];
    this.currentGoals = [];
    this.currentCode = '';
    this.proofStarted = false;
    this.setStatus('idle');
  }
}

// Singleton instance
let serviceInstance: CoqService | null = null;

// FIX #1: Update callbacks on existing instance instead of ignoring them
export function getCoqService(callbacks: CoqServiceCallbacks = {}): CoqService {
  if (!serviceInstance) {
    serviceInstance = new CoqService(callbacks);
  } else if (Object.keys(callbacks).length > 0) {
    // Update callbacks on existing instance to prevent stale closures
    serviceInstance.updateCallbacks(callbacks);
  }
  return serviceInstance;
}

export function resetCoqService(): void {
  serviceInstance?.destroy();
  serviceInstance = null;
}
