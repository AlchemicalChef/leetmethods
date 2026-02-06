'use client';

import type { CoqGoal, VerificationResult, CoqWorkerStatus } from './types';
import { checkForbiddenTactics, isProofComplete } from './verifier';
import { parseStatements, isProofStart, parseGoalData } from './coq-parser';

export interface CoqServiceCallbacks {
  onStatusChange?: (status: CoqWorkerStatus) => void;
  onGoalsUpdate?: (goals: CoqGoal[]) => void;
  onMessage?: (message: { type: 'info' | 'error' | 'warning' | 'notice' | 'success'; content: string }) => void;
  onError?: (error: string) => void;
  onReady?: () => void;
  onExecutionProgress?: (executed: number, total: number) => void;
  onPositionChange?: (charOffset: number) => void;
}

/**
 * CoqService - Iframe-isolated jsCoq integration
 *
 * Runs jsCoq inside a hidden iframe to completely isolate it from the
 * Next.js environment. Communicates via postMessage.
 *
 * Running jsCoq directly in the Next.js page causes stm.ml assertion failures
 * due to state machine conflicts. The iframe approach gives jsCoq a clean
 * browser context that avoids these issues.
 */
export class CoqService {
  private status: CoqWorkerStatus = 'idle';
  private callbacks: CoqServiceCallbacks;
  private iframe: HTMLIFrameElement | null = null;
  private currentCode: string = '';
  private executedStatements: string[] = [];
  private proofStarted: boolean = false;
  private initPromise: Promise<void> | null = null;
  private currentGoals: CoqGoal[] = [];
  private executionError: string | null = null;
  private codeSyncPending: boolean = false;
  private messageId = 0;
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  private pendingMessages = new Map<number, { resolve: (data: any) => void; reject: (err: Error) => void; timeout: ReturnType<typeof setTimeout> }>();
  private messageHandler: ((event: MessageEvent) => void) | null = null;
  private initTimeout: ReturnType<typeof setTimeout> | null = null;
  private goalResolvers: Array<() => void> = [];

  constructor(callbacks: CoqServiceCallbacks = {}) {
    this.callbacks = callbacks;
  }

  updateCallbacks(callbacks: CoqServiceCallbacks): void {
    this.callbacks = callbacks;
  }

  private setStatus(status: CoqWorkerStatus): void {
    this.status = status;
    this.callbacks.onStatusChange?.(status);
  }

  getStatus(): CoqWorkerStatus {
    return this.status;
  }

  async initialize(): Promise<void> {
    if (this.initPromise) {
      return this.initPromise;
    }

    this.initPromise = this.doInitialize();
    return this.initPromise;
  }

  private async doInitialize(): Promise<void> {
    if (this.iframe) {
      this.setStatus('ready');
      this.callbacks.onReady?.();
      return;
    }

    this.setStatus('loading');

    try {
      if (typeof window === 'undefined') {
        throw new Error('jsCoq requires browser environment');
      }

      // Create hidden iframe with jsCoq worker page
      await this.createIframe();

      this.setStatus('ready');
      this.callbacks.onReady?.();
      this.callbacks.onMessage?.({ type: 'info', content: 'Coq runtime initialized' });
    } catch (error) {
      console.error('Failed to initialize jsCoq:', error);
      this.setStatus('error');
      const errorMsg = error instanceof Error ? error.message : 'Failed to initialize Coq runtime';
      this.callbacks.onError?.(errorMsg);
      this.callbacks.onMessage?.({ type: 'error', content: errorMsg });
      throw error;
    }
  }

  private createIframe(): Promise<void> {
    return new Promise((resolve, reject) => {
      // Clean up any existing iframe
      if (this.iframe) {
        this.iframe.remove();
        this.iframe = null;
      }

      // Set up message handler BEFORE creating iframe
      this.messageHandler = (event: MessageEvent) => {
        // Only accept messages from our own iframe, same origin
        if (event.origin !== window.location.origin) return;
        if (this.iframe && event.source !== this.iframe.contentWindow) return;
        const data = event.data;
        if (!data?.type?.startsWith('coq-')) return;

        switch (data.type) {
          case 'coq-ready':
            if (this.initTimeout) {
              clearTimeout(this.initTimeout);
              this.initTimeout = null;
            }
            resolve();
            break;

          case 'coq-error':
            if (this.initTimeout) {
              clearTimeout(this.initTimeout);
              this.initTimeout = null;
            }
            reject(new Error(data.error));
            break;

          case 'coq-goals':
            this.handleGoalInfo(data.goals);
            break;

          case 'coq-exec-error':
            this.executionError = data.error;
            this.callbacks.onMessage?.({ type: 'error', content: data.error });
            break;

          case 'coq-log-error':
            this.executionError = data.error;
            break;

          case 'coq-added-axiom':
            this.callbacks.onMessage?.({ type: 'warning', content: 'Proof contains an unproven axiom (Admitted). Complete the proof to submit.' });
            break;

          case 'coq-result': {
            const pending = this.pendingMessages.get(data.id);
            if (pending) {
              clearTimeout(pending.timeout);
              this.pendingMessages.delete(data.id);
              if (data.error) {
                pending.reject(new Error(data.error));
              } else {
                pending.resolve(data);
              }
            }
            break;
          }

          case 'coq-pong': {
            const pend = this.pendingMessages.get(data.id);
            if (pend) {
              clearTimeout(pend.timeout);
              this.pendingMessages.delete(data.id);
              pend.resolve(data);
            }
            break;
          }
        }
      };
      window.addEventListener('message', this.messageHandler);

      // Create iframe pointing to the jsCoq worker page
      const iframe = document.createElement('iframe');
      iframe.src = `/coq-worker.html?v=${Date.now()}`;
      iframe.sandbox.add('allow-scripts', 'allow-same-origin');
      iframe.style.cssText = 'position: fixed; left: 0; top: 0; width: 800px; height: 600px; opacity: 0; pointer-events: none; z-index: -9999; border: none;';
      document.body.appendChild(iframe);
      this.iframe = iframe;

      // Timeout for initialization
      this.initTimeout = setTimeout(() => {
        this.initTimeout = null;
        if (this.status === 'loading') {
          reject(new Error('Coq initialization timeout (60s)'));
        }
      }, 60000);
    });
  }

  /** Send a command to the iframe and wait for the result */
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  private sendCommand(cmd: string, args: Record<string, unknown> = {}): Promise<any> {
    return new Promise((resolve, reject) => {
      if (!this.iframe?.contentWindow) {
        reject(new Error('Iframe not available'));
        return;
      }

      const id = ++this.messageId;

      const timeout = setTimeout(() => {
        if (this.pendingMessages.has(id)) {
          this.pendingMessages.delete(id);
          reject(new Error(`Command ${cmd} timeout`));
        }
      }, 30000);

      this.pendingMessages.set(id, { resolve, reject, timeout });
      this.iframe.contentWindow.postMessage({ id, cmd, args }, window.location.origin);
    });
  }

  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  private handleGoalInfo(goalData: any): void {
    const goals = parseGoalData(goalData);
    this.currentGoals = goals;
    this.callbacks.onGoalsUpdate?.(goals);

    // Resolve any promises waiting for goal updates
    const resolvers = this.goalResolvers;
    this.goalResolvers = [];
    resolvers.forEach(r => r());
  }

  /** Wait for the next goal update (or timeout) */
  private waitForGoals(timeoutMs: number): Promise<void> {
    return new Promise(resolve => {
      const timer = setTimeout(() => {
        this.goalResolvers = this.goalResolvers.filter(r => r !== wrappedResolve);
        resolve();
      }, timeoutMs);
      const wrappedResolve = () => {
        clearTimeout(timer);
        resolve();
      };
      this.goalResolvers.push(wrappedResolve);
    });
  }

  // stripPpTags and ppToString are now imported from ./coq-parser

  setCode(code: string): void {
    this.currentCode = code;
    this.codeSyncPending = true;
    this.sendCommand('set-code', { code })
      .then(() => { this.codeSyncPending = false; })
      .catch(() => { this.codeSyncPending = true; });
  }

  private async ensureCodeSynced(): Promise<void> {
    if (this.codeSyncPending) {
      await this.sendCommand('set-code', { code: this.currentCode });
      this.codeSyncPending = false;
    }
  }

  getCode(): string {
    return this.currentCode;
  }

  isProofStarted(): boolean {
    return this.proofStarted;
  }

  // parseStatements and isProofStart are imported from ./coq-parser

  private computeExecutedOffset(): number {
    if (this.executedStatements.length === 0) return 0;
    let offset = 0;
    const code = this.currentCode;
    for (const stmt of this.executedStatements) {
      const idx = code.indexOf(stmt, offset);
      if (idx === -1) break;
      offset = idx + stmt.length;
    }
    return offset;
  }

  private firePositionChange(): void {
    this.callbacks.onPositionChange?.(this.computeExecutedOffset());
  }

  async executeNext(): Promise<void> {
    if (!this.iframe) {
      throw new Error('Coq not initialized');
    }

    if (this.status !== 'ready') {
      throw new Error('Coq is not ready');
    }

    this.setStatus('busy');

    try {
      await this.ensureCodeSynced();
      const result = await this.sendCommand('exec-next');

      if (result.hasMore !== false) {
        const statements = parseStatements(this.currentCode);
        const nextIndex = this.executedStatements.length;
        if (nextIndex < statements.length) {
          const statement = statements[nextIndex];
          this.executedStatements.push(statement);
          if (isProofStart(statement)) {
            this.proofStarted = true;
          }
        }
      }

      this.setStatus('ready');
      this.firePositionChange();
    } catch (error) {
      this.setStatus('error');
      this.callbacks.onError?.(error instanceof Error ? error.message : 'Execution failed');
      throw error;
    }
  }

  async executePrev(): Promise<void> {
    if (!this.iframe) {
      throw new Error('Coq not initialized');
    }

    if (this.status !== 'ready') {
      throw new Error('Coq is not ready');
    }

    this.setStatus('busy');

    try {
      await this.sendCommand('exec-prev');

      if (this.executedStatements.length > 0) {
        this.executedStatements.pop();
      }

      this.setStatus('ready');
      this.firePositionChange();
    } catch (error) {
      this.setStatus('error');
      this.callbacks.onError?.(error instanceof Error ? error.message : 'Undo failed');
      throw error;
    }
  }

  async executeAll(): Promise<{ stoppedAt?: string; error?: string }> {
    if (!this.iframe) {
      throw new Error('Coq not initialized');
    }

    if (this.status !== 'ready') {
      throw new Error('Coq is not ready');
    }

    this.setStatus('busy');
    this.executionError = null;

    try {
      await this.ensureCodeSynced();
      const statements = parseStatements(this.currentCode);
      const total = statements.length;

      const result = await this.sendCommand('exec-all');

      const actualProcessed = result.processedCount ?? 0;

      // Update tracking
      this.executedStatements = statements.slice(0, actualProcessed);
      for (const stmt of this.executedStatements) {
        if (isProofStart(stmt)) {
          this.proofStarted = true;
        }
      }

      let stoppedAt: string | undefined;
      if (result.errors?.length > 0) {
        this.executionError = result.errors[0];
        stoppedAt = result.errors[0];
      }

      this.callbacks.onExecutionProgress?.(this.executedStatements.length, total);
      this.setStatus('ready');
      this.firePositionChange();

      return { stoppedAt, error: this.executionError || undefined };
    } catch (error) {
      this.setStatus('error');
      const errorMsg = error instanceof Error ? error.message : 'Execution failed';
      this.executionError = errorMsg;
      this.callbacks.onError?.(errorMsg);
      throw error;
    }
  }

  async reset(): Promise<void> {
    this.setStatus('busy');

    try {
      if (this.iframe) {
        await this.sendCommand('reset');
      }

      this.executedStatements = [];
      this.proofStarted = false;
      this.currentGoals = [];
      this.executionError = null;
      this.goalResolvers = [];
      this.callbacks.onGoalsUpdate?.([]);
      this.setStatus('ready');
      this.firePositionChange();
    } catch (error) {
      this.setStatus('error');
      this.callbacks.onError?.(error instanceof Error ? error.message : 'Reset failed');
      throw error;
    }
  }

  async verify(
    prelude: string,
    userCode: string,
    forbiddenTactics: string[] = ['admit', 'Admitted']
  ): Promise<VerificationResult> {
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

    await this.reset();
    this.executionError = null;
    const fullCode = `${prelude}\n\n${userCode}`;
    this.currentCode = fullCode;

    // Set code in the iframe
    await this.sendCommand('set-code', { code: fullCode });

    try {
      const execResult = await this.executeAll();

      // Wait for goals to propagate via postMessage
      await this.waitForGoals(500);

      const goals = this.currentGoals;
      const hasTerminator = isProofComplete(userCode);
      const errors: string[] = [];

      if (execResult.stoppedAt) {
        errors.push(execResult.error || `Execution stopped at: ${execResult.stoppedAt}`);
      }

      if (this.executionError && !errors.includes(this.executionError)) {
        errors.push(this.executionError);
      }

      const isComplete = goals.length === 0 && hasTerminator && errors.length === 0;

      if (goals.length > 0) {
        errors.push(`Proof incomplete: ${goals.length} goal(s) remaining`);
      }

      if (hasTerminator && goals.length > 0) {
        errors.push('Proof terminator failed: proof has unresolved goals');
      }

      return {
        success: isComplete,
        goals,
        errors,
        messages: [],
        hasForbiddenTactics: false,
        forbiddenTacticsFound: [],
        isComplete,
      };
    } catch (error) {
      return {
        success: false,
        goals: [],
        errors: [error instanceof Error ? error.message : 'Verification failed'],
        messages: [],
        hasForbiddenTactics: false,
        forbiddenTacticsFound: [],
        isComplete: false,
      };
    }
  }

  destroy(): void {
    // Clear init timeout
    if (this.initTimeout) {
      clearTimeout(this.initTimeout);
      this.initTimeout = null;
    }

    // Remove message handler
    if (this.messageHandler) {
      window.removeEventListener('message', this.messageHandler);
      this.messageHandler = null;
    }

    // Remove iframe (kills the worker automatically)
    if (this.iframe) {
      this.iframe.remove();
      this.iframe = null;
    }

    // Clear pending messages and their timeouts
    this.pendingMessages.forEach((pending) => {
      clearTimeout(pending.timeout);
      pending.reject(new Error('Service destroyed'));
    });
    this.pendingMessages.clear();

    this.executedStatements = [];
    this.proofStarted = false;
    this.currentCode = '';
    this.currentGoals = [];
    this.executionError = null;
    this.codeSyncPending = false;
    this.goalResolvers = [];
    this.initPromise = null;
    this.setStatus('idle');
  }
}

// Singleton instance - persists across React remounts
let serviceInstance: CoqService | null = null;
let isInitializing = false;

export function getCoqService(callbacks: CoqServiceCallbacks = {}): CoqService {
  if (!serviceInstance) {
    serviceInstance = new CoqService(callbacks);
  } else if (Object.keys(callbacks).length > 0) {
    serviceInstance.updateCallbacks(callbacks);
  }
  return serviceInstance;
}

export function resetCoqService(): void {
  // Don't destroy during initialization (React Strict Mode causes double-mount)
  if (isInitializing) {
    return;
  }
  serviceInstance?.destroy();
  serviceInstance = null;
}

export function setInitializing(value: boolean): void {
  isInitializing = value;
}
