'use client';

import type { CoqGoal, CoqHypothesis, VerificationResult, CoqWorkerStatus } from './types';
import { checkForbiddenTactics, isProofComplete } from './verifier';

export interface CoqServiceCallbacks {
  onStatusChange?: (status: CoqWorkerStatus) => void;
  onGoalsUpdate?: (goals: CoqGoal[]) => void;
  onMessage?: (message: { type: 'info' | 'error' | 'warning' | 'notice' | 'success'; content: string }) => void;
  onError?: (error: string) => void;
  onReady?: () => void;
  onExecutionProgress?: (executed: number, total: number) => void;
}

// jsCoq Manager interface
interface JsCoqManager {
  when_ready: Promise<void>;
  goNext(focus?: boolean): boolean;
  goPrev(focus?: boolean): boolean;
  goCursor(): void;
  reset(): Promise<void>;
  provider?: {
    snippets?: Array<{
      editor?: {
        getValue(): string;
        setValue(value: string): void;
      };
    }>;
  };
  layout?: {
    proof?: HTMLElement;
  };
}

// Global JsCoq type
declare global {
  interface Window {
    JsCoq?: {
      start(ids: string[] | string, options?: Record<string, unknown>): Promise<JsCoqManager>;
    };
  }
}

/**
 * CoqService - Self-hosted jsCoq integration
 *
 * Uses jsCoq served from /jscoq/ in the public directory.
 */
export class CoqService {
  private status: CoqWorkerStatus = 'idle';
  private callbacks: CoqServiceCallbacks;
  private coqManager: JsCoqManager | null = null;
  private currentCode: string = '';
  private executedStatements: string[] = [];
  private proofStarted: boolean = false;
  private initPromise: Promise<void> | null = null;
  private containerId: string;
  private currentGoals: CoqGoal[] = [];
  private goalObserver: MutationObserver | null = null;

  constructor(callbacks: CoqServiceCallbacks = {}) {
    this.callbacks = callbacks;
    this.containerId = `jscoq-container-${Date.now()}`;
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

  private static jscoqLoadPromise: Promise<void> | null = null;

  private async loadJsCoqModule(): Promise<void> {
    // Check if already loaded
    if (window.JsCoq) {
      return;
    }

    // If already loading, wait for that promise
    if (CoqService.jscoqLoadPromise) {
      return CoqService.jscoqLoadPromise;
    }

    // Note: We don't load jsCoq CSS as it contains Bootstrap which conflicts with our styles
    // The jsCoq UI is hidden anyway - we only use the Coq execution engine

    CoqService.jscoqLoadPromise = new Promise((resolve, reject) => {
      // Check if script already exists
      const existingScript = document.querySelector('script[src="/jscoq/loader.js"]');
      if (existingScript) {
        // Script exists, wait for jscoq-loaded event or check if already loaded
        const checkLoaded = () => {
          if (window.JsCoq) {
            resolve();
          } else {
            setTimeout(checkLoaded, 100);
          }
        };
        checkLoaded();
        return;
      }

      const script = document.createElement('script');
      script.type = 'module';
      script.src = '/jscoq/loader.js';

      const handleLoad = () => {
        window.removeEventListener('jscoq-loaded', handleLoad);
        if (window.JsCoq) {
          resolve();
        } else {
          reject(new Error('JsCoq failed to load'));
        }
      };

      window.addEventListener('jscoq-loaded', handleLoad);

      script.onerror = () => {
        window.removeEventListener('jscoq-loaded', handleLoad);
        CoqService.jscoqLoadPromise = null;
        reject(new Error('Failed to load jsCoq script'));
      };

      document.head.appendChild(script);

      // Timeout after 30 seconds
      setTimeout(() => {
        if (!window.JsCoq) {
          window.removeEventListener('jscoq-loaded', handleLoad);
          CoqService.jscoqLoadPromise = null;
          reject(new Error('jsCoq load timeout'));
        }
      }, 30000);
    });

    return CoqService.jscoqLoadPromise;
  }

  private async doInitialize(): Promise<void> {
    if (this.coqManager) {
      this.setStatus('ready');
      this.callbacks.onReady?.();
      return;
    }

    this.setStatus('loading');

    try {
      if (typeof window === 'undefined') {
        throw new Error('jsCoq requires browser environment');
      }

      // Create the jsCoq container
      this.createContainer();

      // Verify element was created
      const textareaId = `${this.containerId}-code`;
      const textarea = document.getElementById(textareaId);
      if (!textarea) {
        throw new Error(`Failed to create textarea element: ${textareaId}`);
      }

      // Wait for DOM to be fully updated before jsCoq tries to find elements
      await new Promise<void>(resolve => {
        requestAnimationFrame(() => {
          requestAnimationFrame(() => resolve());
        });
      });

      // Double-check element is still there and visible to DOM
      const verifyElement = document.getElementById(textareaId);
      if (!verifyElement) {
        throw new Error(`Element disappeared after DOM sync: ${textareaId}`);
      }

      // Load JsCoq module via script tag (webpack doesn't support dynamic import of public files)
      await this.loadJsCoqModule();

      if (!window.JsCoq) {
        throw new Error('JsCoq not available after loading');
      }

      // Final check before starting - element must still exist
      const finalCheck = document.getElementById(textareaId);
      if (!finalCheck) {
        throw new Error(`Element disappeared before JsCoq.start: ${textareaId}`);
      }

      // Start jsCoq with our textarea
      // Note: JsCoq._getopts expects: string=base_path, string=node_modules, array=ids, object=opts
      // Element IDs must be passed as an array
      // Use 'wa' (WebAssembly) backend - the only one we have bundled
      // IMPORTANT: show must be true for jsCoq to initialize - our container is hidden anyway
      this.coqManager = await window.JsCoq.start([textareaId], {
        backend: 'wa',
        prelude: true,
        implicit_libs: true,
        init_pkgs: ['init'],
        all_pkgs: ['coq'],
        show: true,  // Required for initialization to complete
        focus: false,
        editor: { mode: { 'company-coq': false } },
      });

      // Wait for Coq to be ready (with timeout)
      const timeoutPromise = new Promise<never>((_, reject) => {
        setTimeout(() => reject(new Error('Coq initialization timeout (60s)')), 60000);
      });

      await Promise.race([this.coqManager.when_ready, timeoutPromise]);

      // Set up goal observer
      this.setupGoalObserver();

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

  private createContainer(): void {
    // Remove any existing jscoq containers to avoid conflicts
    const existingContainer = document.getElementById(this.containerId);
    if (existingContainer) {
      existingContainer.remove();
    }

    // Also remove standard wrapper if it exists (from previous instances)
    const existingWrapper = document.getElementById('ide-wrapper');
    if (existingWrapper && existingWrapper.dataset.jscoqManaged === 'true') {
      existingWrapper.remove();
    }

    // Create the jsCoq wrapper structure (hidden but accessible)
    // Using STANDARD IDs that jsCoq expects by default
    const container = document.createElement('div');
    container.id = this.containerId;
    container.className = 'jscoq-main';
    // Keep element in DOM flow but hidden - some libraries have issues with off-screen elements
    container.style.cssText = 'position: absolute; left: -9999px; width: 800px; height: 600px; overflow: hidden;';

    // Use standard IDs that jsCoq expects
    const ideWrapper = document.createElement('div');
    ideWrapper.id = 'ide-wrapper';
    ideWrapper.className = 'toggled';
    ideWrapper.dataset.jscoqManaged = 'true';  // Mark for cleanup

    const codeWrapper = document.createElement('div');
    codeWrapper.id = 'code-wrapper';

    const documentDiv = document.createElement('div');
    documentDiv.id = 'document';

    // Textarea still gets unique ID
    const textarea = document.createElement('textarea');
    textarea.id = `${this.containerId}-code`;
    textarea.style.cssText = 'width: 100%; height: 400px;';
    // Pre-populate with a simple comment so jsCoq has something to parse
    textarea.value = '(* LeetMethods Coq Editor *)';

    documentDiv.appendChild(textarea);
    codeWrapper.appendChild(documentDiv);
    ideWrapper.appendChild(codeWrapper);
    container.appendChild(ideWrapper);
    document.body.appendChild(container);
  }

  private setupGoalObserver(): void {
    if (this.coqManager?.layout?.proof) {
      this.goalObserver = new MutationObserver(() => {
        this.parseAndUpdateGoals();
      });
      this.goalObserver.observe(this.coqManager.layout.proof, {
        childList: true,
        subtree: true,
        characterData: true,
      });
    }
  }

  private parseAndUpdateGoals(): void {
    if (!this.coqManager?.layout?.proof) return;

    const proofElement = this.coqManager.layout.proof;
    const goals = this.parseGoalsFromElement(proofElement);
    this.currentGoals = goals;
    this.callbacks.onGoalsUpdate?.(goals);
  }

  private parseGoalsFromElement(element: HTMLElement): CoqGoal[] {
    const goals: CoqGoal[] = [];

    const noGoals = element.querySelector('.no-goals');
    if (noGoals) {
      return [];
    }

    const envElements = element.querySelectorAll('.coq-env');
    envElements.forEach((env, index) => {
      const hypotheses: CoqHypothesis[] = [];

      const hypElements = env.querySelectorAll('.coq-hypothesis');
      hypElements.forEach((hyp) => {
        const labels = hyp.querySelectorAll('label');
        const typeDiv = hyp.querySelector('div:last-child');
        const type = typeDiv?.textContent?.trim() || '';

        labels.forEach((label) => {
          hypotheses.push({
            name: label.textContent?.trim() || '',
            type,
          });
        });
      });

      const hr = env.querySelector('hr');
      const conclusion = hr?.nextElementSibling?.textContent?.trim() ||
                        env.lastElementChild?.textContent?.trim() || '';

      goals.push({
        id: index + 1,
        hypotheses,
        conclusion,
      });
    });

    const pendingGoals = element.querySelectorAll('.coq-subgoal-pending');
    pendingGoals.forEach((pending) => {
      const conclusion = pending.textContent?.replace(/^\d+\s*/, '').trim() || '';
      goals.push({
        id: goals.length + 1,
        hypotheses: [],
        conclusion,
      });
    });

    return goals;
  }

  setCode(code: string): void {
    this.currentCode = code;

    if (this.coqManager?.provider?.snippets?.[0]?.editor) {
      this.coqManager.provider.snippets[0].editor.setValue(code);
    }
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
    if (!this.coqManager) {
      throw new Error('Coq not initialized');
    }

    if (this.status !== 'ready') {
      throw new Error('Coq is not ready');
    }

    this.setStatus('busy');

    try {
      const result = this.coqManager.goNext(false);

      await new Promise(resolve => setTimeout(resolve, 150));

      if (result !== false) {
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

      this.parseAndUpdateGoals();
      this.setStatus('ready');
    } catch (error) {
      this.setStatus('error');
      this.callbacks.onError?.(error instanceof Error ? error.message : 'Execution failed');
      throw error;
    }
  }

  async executePrev(): Promise<void> {
    if (!this.coqManager) {
      throw new Error('Coq not initialized');
    }

    if (this.status !== 'ready') {
      throw new Error('Coq is not ready');
    }

    this.setStatus('busy');

    try {
      this.coqManager.goPrev(false);

      await new Promise(resolve => setTimeout(resolve, 150));

      if (this.executedStatements.length > 0) {
        this.executedStatements.pop();
      }

      this.parseAndUpdateGoals();
      this.setStatus('ready');
    } catch (error) {
      this.setStatus('error');
      this.callbacks.onError?.(error instanceof Error ? error.message : 'Undo failed');
      throw error;
    }
  }

  async executeAll(): Promise<void> {
    if (!this.coqManager) {
      throw new Error('Coq not initialized');
    }

    if (this.status !== 'ready') {
      throw new Error('Coq is not ready');
    }

    this.setStatus('busy');

    try {
      const statements = this.parseStatements(this.currentCode);
      const total = statements.length;

      for (let i = this.executedStatements.length; i < total; i++) {
        const result = this.coqManager.goNext(false);
        if (result === false) break;

        const statement = statements[i];
        this.executedStatements.push(statement);

        if (statement.toLowerCase().includes('proof')) {
          this.proofStarted = true;
        }

        this.callbacks.onExecutionProgress?.(i + 1, total);
        await new Promise(resolve => setTimeout(resolve, 100));
      }

      this.parseAndUpdateGoals();
      this.setStatus('ready');
    } catch (error) {
      this.setStatus('error');
      this.callbacks.onError?.(error instanceof Error ? error.message : 'Execution failed');
      throw error;
    }
  }

  async reset(): Promise<void> {
    this.setStatus('busy');

    try {
      if (this.coqManager) {
        await this.coqManager.reset();
      }

      this.executedStatements = [];
      this.proofStarted = false;
      this.currentGoals = [];
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
    const fullCode = `${prelude}\n\n${userCode}`;
    this.setCode(fullCode);

    try {
      await this.executeAll();

      const goals = this.currentGoals;
      const hasQed = isProofComplete(userCode);
      const isComplete = goals.length === 0 && hasQed;

      return {
        success: isComplete,
        goals,
        errors: [],
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
    this.goalObserver?.disconnect();
    this.goalObserver = null;
    this.executedStatements = [];
    this.proofStarted = false;
    this.currentCode = '';
    this.currentGoals = [];
    this.coqManager = null;
    this.initPromise = null;
    this.setStatus('idle');

    // Clean up our container
    const container = document.getElementById(this.containerId);
    if (container) {
      container.remove();
    }

    // Also clean up the standard wrapper if it was ours
    const ideWrapper = document.getElementById('ide-wrapper');
    if (ideWrapper && ideWrapper.dataset.jscoqManaged === 'true') {
      ideWrapper.remove();
    }
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
