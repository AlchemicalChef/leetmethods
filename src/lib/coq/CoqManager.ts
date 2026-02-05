'use client';

import type { CoqGoal, CoqMessage, VerificationResult, CoqWorkerStatus } from './types';
import { checkForbiddenTactics, isProofComplete } from './verifier';

export interface CoqManagerCallbacks {
  onStatusChange?: (status: CoqWorkerStatus) => void;
  onGoalsUpdate?: (goals: CoqGoal[]) => void;
  onMessage?: (message: CoqMessage) => void;
  onError?: (error: string) => void;
  onReady?: () => void;
}

declare global {
  interface Window {
    JsCoq?: {
      start: (path: string | undefined, ids: string[], options?: Record<string, unknown>) => Promise<CoqManagerInstance>;
    };
    coqManager?: CoqManagerInstance;
  }
}

interface CoqManagerInstance {
  when_ready: Promise<void>;
  editor: {
    getValue(): string;
    setValue(value: string): void;
  };
  provider?: {
    goals?: CoqGoal[];
  };
  goNext(): Promise<void>;
  goPrev(): Promise<void>;
  goEnd(): Promise<void>;
  reset(): Promise<void>;
  interruptRequest(): void;
}

export class CoqManager {
  private status: CoqWorkerStatus = 'idle';
  private callbacks: CoqManagerCallbacks;
  private jscoqInstance: CoqManagerInstance | null = null;
  private initialized = false;
  private containerId: string;
  private goalObserver: MutationObserver | null = null;

  constructor(containerId: string, callbacks: CoqManagerCallbacks = {}) {
    this.containerId = containerId;
    this.callbacks = callbacks;
  }

  // FIX #12: Allow updating callbacks after construction
  updateCallbacks(callbacks: CoqManagerCallbacks): void {
    this.callbacks = callbacks;
  }

  // FIX #12: Allow checking/updating container ID
  getContainerId(): string {
    return this.containerId;
  }

  async initialize(): Promise<void> {
    if (this.initialized || typeof window === 'undefined') {
      return;
    }

    this.setStatus('loading');

    try {
      // Load jsCoq script dynamically
      await this.loadJsCoqScript();

      if (!window.JsCoq) {
        throw new Error('JsCoq failed to load');
      }

      // Initialize jsCoq with our container
      this.jscoqInstance = await window.JsCoq.start(undefined, [this.containerId], {
        init_pkgs: ['init', 'coq-base', 'coq-arith'],
        prelude: true,
        frontend: 'cm5',
        theme: 'light',
        show: false, // We'll manage the panel ourselves
        focus: true,
        editor: {
          mode: { name: 'coq' },
          lineNumbers: true,
          theme: 'default',
        },
      });

      window.coqManager = this.jscoqInstance;

      // Wait for Coq to be ready
      await this.jscoqInstance.when_ready;

      // Set up goal observation
      this.setupGoalObserver();

      this.initialized = true;
      this.setStatus('ready');
      this.callbacks.onReady?.();
    } catch (error) {
      this.setStatus('error');
      const message = error instanceof Error ? error.message : 'Failed to initialize Coq';
      this.callbacks.onError?.(message);
      throw error;
    }
  }

  private async loadJsCoqScript(): Promise<void> {
    if (window.JsCoq) {
      return;
    }

    return new Promise((resolve, reject) => {
      // jsCoq is loaded from CDN
      const script = document.createElement('script');
      script.src = 'https://jscoq.github.io/node_modules/jscoq/jscoq.js';
      script.type = 'module';
      script.async = true;
      script.onload = () => resolve();
      script.onerror = () => reject(new Error('Failed to load jsCoq script'));
      document.head.appendChild(script);
    });
  }

  private setupGoalObserver(): void {
    // Observe the goals panel for changes
    const goalsPanel = document.querySelector('.coq-goals');
    if (goalsPanel) {
      this.goalObserver = new MutationObserver(() => {
        this.parseAndEmitGoals();
      });
      this.goalObserver.observe(goalsPanel, {
        childList: true,
        subtree: true,
        characterData: true,
      });
    }
  }

  private parseAndEmitGoals(): void {
    const goalsElement = document.querySelector('.coq-goals');
    if (!goalsElement) return;

    const goals = this.parseGoalsFromDOM(goalsElement);
    this.callbacks.onGoalsUpdate?.(goals);
  }

  private parseGoalsFromDOM(element: Element): CoqGoal[] {
    const goals: CoqGoal[] = [];
    const goalElements = element.querySelectorAll('.goal');

    goalElements.forEach((goalEl, index) => {
      const hypotheses: CoqGoal['hypotheses'] = [];

      // Parse hypotheses
      const hypElements = goalEl.querySelectorAll('.hyp');
      hypElements.forEach((hypEl) => {
        const nameEl = hypEl.querySelector('.hyp-name');
        const typeEl = hypEl.querySelector('.hyp-type');
        if (nameEl && typeEl) {
          hypotheses.push({
            name: nameEl.textContent?.trim() || '',
            type: typeEl.textContent?.trim() || '',
          });
        }
      });

      // Parse conclusion
      const conclusionEl = goalEl.querySelector('.goal-conclusion');
      const conclusion = conclusionEl?.textContent?.trim() || '';

      goals.push({
        id: index + 1,
        hypotheses,
        conclusion,
      });
    });

    return goals;
  }

  private setStatus(status: CoqWorkerStatus): void {
    this.status = status;
    this.callbacks.onStatusChange?.(status);
  }

  getStatus(): CoqWorkerStatus {
    return this.status;
  }

  async executeNext(): Promise<void> {
    if (!this.jscoqInstance || this.status !== 'ready') {
      throw new Error('Coq is not ready');
    }

    this.setStatus('busy');
    try {
      await this.jscoqInstance.goNext();
      this.parseAndEmitGoals();
    } finally {
      this.setStatus('ready');
    }
  }

  async executePrev(): Promise<void> {
    if (!this.jscoqInstance || this.status !== 'ready') {
      throw new Error('Coq is not ready');
    }

    this.setStatus('busy');
    try {
      await this.jscoqInstance.goPrev();
      this.parseAndEmitGoals();
    } finally {
      this.setStatus('ready');
    }
  }

  async executeAll(): Promise<void> {
    if (!this.jscoqInstance || this.status !== 'ready') {
      throw new Error('Coq is not ready');
    }

    this.setStatus('busy');
    try {
      await this.jscoqInstance.goEnd();
      this.parseAndEmitGoals();
    } finally {
      this.setStatus('ready');
    }
  }

  async reset(): Promise<void> {
    if (!this.jscoqInstance) {
      return;
    }

    this.setStatus('busy');
    try {
      await this.jscoqInstance.reset();
      this.callbacks.onGoalsUpdate?.([]);
    } finally {
      this.setStatus('ready');
    }
  }

  interrupt(): void {
    this.jscoqInstance?.interruptRequest();
  }

  getCode(): string {
    return this.jscoqInstance?.editor.getValue() || '';
  }

  setCode(code: string): void {
    if (this.jscoqInstance?.editor) {
      this.jscoqInstance.editor.setValue(code);
    }
  }

  async verify(
    prelude: string,
    userCode: string,
    forbiddenTactics: string[] = ['admit', 'Admitted']
  ): Promise<VerificationResult> {
    // Check for forbidden tactics first
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

    // Set the full code and execute
    const fullCode = `${prelude}\n\n${userCode}`;
    this.setCode(fullCode);

    try {
      await this.executeAll();

      // Get current goals
      const goalsElement = document.querySelector('.coq-goals');
      const goals = goalsElement ? this.parseGoalsFromDOM(goalsElement) : [];

      // Check for errors in the message panel
      const errors: string[] = [];
      const errorElements = document.querySelectorAll('.coq-message.error');
      errorElements.forEach((el) => {
        const text = el.textContent?.trim();
        if (text) errors.push(text);
      });

      const isComplete = goals.length === 0 && errors.length === 0 && isProofComplete(userCode);

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
    this.goalObserver?.disconnect();
    this.goalObserver = null;
    this.jscoqInstance = null;
    this.initialized = false;
    this.setStatus('idle');
  }
}

// FIX #12: Store instances by containerId to support multiple containers
const coqManagerInstances: Map<string, CoqManager> = new Map();

export function getCoqManager(containerId: string, callbacks: CoqManagerCallbacks = {}): CoqManager {
  let instance = coqManagerInstances.get(containerId);

  if (!instance) {
    instance = new CoqManager(containerId, callbacks);
    coqManagerInstances.set(containerId, instance);
  } else if (Object.keys(callbacks).length > 0) {
    // Update callbacks on existing instance to prevent stale closures
    instance.updateCallbacks(callbacks);
  }

  return instance;
}

export function resetCoqManager(containerId?: string): void {
  if (containerId) {
    const instance = coqManagerInstances.get(containerId);
    instance?.destroy();
    coqManagerInstances.delete(containerId);
  } else {
    // Reset all instances
    coqManagerInstances.forEach((instance) => instance.destroy());
    coqManagerInstances.clear();
  }
}
