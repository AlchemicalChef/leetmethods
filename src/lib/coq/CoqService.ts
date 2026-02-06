'use client';

import type { CoqGoal, VerificationResult, CoqWorkerStatus } from './types';
import { checkForbiddenTactics, isProofComplete } from './verifier';

export interface CoqServiceCallbacks {
  onStatusChange?: (status: CoqWorkerStatus) => void;
  onGoalsUpdate?: (goals: CoqGoal[]) => void;
  onMessage?: (message: { type: 'info' | 'error' | 'warning' | 'notice' | 'success'; content: string }) => void;
  onError?: (error: string) => void;
  onReady?: () => void;
  onExecutionProgress?: (executed: number, total: number) => void;
}

/**
 * CoqService - Iframe-isolated jsCoq integration
 *
 * Runs jsCoq inside a hidden iframe to completely isolate it from the
 * Next.js environment. Communicates via postMessage.
 *
 * The standalone test page (jscoq-test.html) works perfectly, but running
 * jsCoq directly in the Next.js page causes stm.ml assertion failures.
 * The iframe approach gives jsCoq a clean browser context.
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
  private messageId = 0;
  private pendingMessages = new Map<number, { resolve: (data: any) => void; reject: (err: Error) => void }>();
  private messageHandler: ((event: MessageEvent) => void) | null = null;

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
        const data = event.data;
        if (!data?.type?.startsWith('coq-')) return;

        switch (data.type) {
          case 'coq-ready':
            console.log('[CoqService] Coq ready (via iframe)');
            resolve();
            break;

          case 'coq-error':
            console.error('[CoqService] Coq init error:', data.error);
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

          case 'coq-result': {
            const pending = this.pendingMessages.get(data.id);
            if (pending) {
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
      iframe.style.cssText = 'position: fixed; left: 0; top: 0; width: 800px; height: 600px; opacity: 0; pointer-events: none; z-index: -9999; border: none;';
      document.body.appendChild(iframe);
      this.iframe = iframe;

      // Timeout for initialization
      setTimeout(() => {
        if (this.status === 'loading') {
          reject(new Error('Coq initialization timeout (60s)'));
        }
      }, 60000);
    });
  }

  /** Send a command to the iframe and wait for the result */
  private sendCommand(cmd: string, args: Record<string, unknown> = {}): Promise<any> {
    return new Promise((resolve, reject) => {
      if (!this.iframe?.contentWindow) {
        reject(new Error('Iframe not available'));
        return;
      }

      const id = ++this.messageId;
      this.pendingMessages.set(id, { resolve, reject });

      this.iframe.contentWindow.postMessage({ id, cmd, args }, '*');

      // Timeout for individual commands
      setTimeout(() => {
        if (this.pendingMessages.has(id)) {
          this.pendingMessages.delete(id);
          reject(new Error(`Command ${cmd} timeout`));
        }
      }, 30000);
    });
  }

  private handleGoalInfo(goalData: any): void {
    if (!goalData?.goals) {
      this.currentGoals = [];
      this.callbacks.onGoalsUpdate?.([]);
      return;
    }

    const goals: CoqGoal[] = goalData.goals.map((g: any, index: number) => ({
      id: index + 1,
      hypotheses: (g.hyp || []).map(([names, type]: [string[], string]) => ({
        name: names.join(', '),
        type: this.stripPpTags(type),
      })),
      conclusion: this.stripPpTags(g.ccl),
    }));

    this.currentGoals = goals;
    this.callbacks.onGoalsUpdate?.(goals);
  }

  private stripPpTags(s: string): string {
    if (typeof s !== 'string') return String(s);
    return s.replace(/<\/?Pp_[^>]*>/g, '').replace(/<\/?[a-z_]+>/gi, '').trim();
  }

  setCode(code: string): void {
    this.currentCode = code;
    // Fire and forget - the code will be sent when needed
    this.sendCommand('set-code', { code }).catch(() => {});
  }

  getCode(): string {
    return this.currentCode;
  }

  isProofStarted(): boolean {
    return this.proofStarted;
  }

  private parseStatements(code: string): string[] {
    const statements: string[] = [];
    let current = '';
    let commentDepth = 0;
    let inString = false;

    for (let i = 0; i < code.length; i++) {
      const char = code[i];
      const next = code[i + 1];

      if (char === '(' && next === '*' && !inString) {
        commentDepth++;
        current += char;
        continue;
      }

      if (char === '*' && next === ')' && commentDepth > 0 && !inString) {
        commentDepth--;
        current += char;
        continue;
      }

      if (char === '"' && commentDepth === 0) {
        inString = !inString;
      }

      current += char;

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

  async executeNext(): Promise<void> {
    if (!this.iframe) {
      throw new Error('Coq not initialized');
    }

    if (this.status !== 'ready') {
      throw new Error('Coq is not ready');
    }

    this.setStatus('busy');

    try {
      const result = await this.sendCommand('exec-next');

      if (result.hasMore !== false) {
        const statements = this.parseStatements(this.currentCode);
        const nextIndex = this.executedStatements.length;
        if (nextIndex < statements.length) {
          const statement = statements[nextIndex];
          this.executedStatements.push(statement);
          if (statement.toLowerCase().includes('proof')) {
            this.proofStarted = true;
          }
        }
      }

      this.setStatus('ready');
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
      const statements = this.parseStatements(this.currentCode);
      const total = statements.length;

      const result = await this.sendCommand('exec-all');

      const actualProcessed = result.processedCount ?? 0;

      // Update tracking
      this.executedStatements = statements.slice(0, actualProcessed);
      for (const stmt of this.executedStatements) {
        if (stmt.toLowerCase().includes('proof')) {
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
      this.callbacks.onGoalsUpdate?.([]);
      this.setStatus('ready');
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

      // Wait a bit for goals to propagate via postMessage
      await new Promise(resolve => setTimeout(resolve, 200));

      const goals = this.currentGoals;
      const hasQed = isProofComplete(userCode);
      const errors: string[] = [];

      console.log('[CoqService.verify] Debug info:', {
        execResult,
        goalsCount: goals.length,
        hasQed,
        executedStatements: this.executedStatements,
        totalStatements: this.parseStatements(fullCode).length,
        executionError: this.executionError,
      });

      if (execResult.stoppedAt) {
        errors.push(execResult.error || `Execution stopped at: ${execResult.stoppedAt}`);
      }

      if (this.executionError && !errors.includes(this.executionError)) {
        errors.push(this.executionError);
      }

      const isComplete = goals.length === 0 && hasQed && errors.length === 0;

      if (goals.length > 0) {
        errors.push(`Proof incomplete: ${goals.length} goal(s) remaining`);
      }

      if (hasQed && goals.length > 0) {
        errors.push('Qed failed: proof has unresolved goals');
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

    // Clear pending messages
    for (const [, pending] of this.pendingMessages) {
      pending.reject(new Error('Service destroyed'));
    }
    this.pendingMessages.clear();

    this.executedStatements = [];
    this.proofStarted = false;
    this.currentCode = '';
    this.currentGoals = [];
    this.executionError = null;
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
