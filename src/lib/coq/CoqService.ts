/**
 * @module CoqService
 *
 * Central singleton service for communicating with jsCoq, the JavaScript/WASM
 * port of the Coq proof assistant. This is the heart of the LeetMethods
 * architecture: it manages the hidden iframe that hosts jsCoq and provides a
 * high-level API for executing Coq statements, verifying proofs, and tracking
 * proof state.
 *
 * ## Architecture: Why an Iframe?
 *
 * jsCoq cannot run directly inside a Next.js page. The Coq state machine
 * (stm.ml) makes assumptions about being the sole occupant of a browser
 * context. When loaded alongside React's hydration and Hot Module Replacement,
 * stm.ml throws assertion failures due to conflicting state machine transitions.
 *
 * The solution is **complete isolation via a hidden iframe** that loads
 * `public/coq-worker.html`. This gives jsCoq its own clean browser context.
 * All communication happens through the `window.postMessage` IPC channel:
 *
 * ```
 * React Components (ProblemSolver, TutorialPage)
 *   -> useCoqSession hook (shared lifecycle management)
 *     -> CoqService singleton (this file)
 *       -> hidden <iframe> (public/coq-worker.html)
 *         -> jsCoq 0.17.1 ('js' backend, NOT 'wa')
 *       <- postMessage IPC responses
 * ```
 *
 * ## Singleton Pattern
 *
 * CoqService uses a module-level singleton (`getCoqService()`) so the expensive
 * iframe initialization (~5-10 seconds) persists across React component remounts
 * and page navigations. The `setInitializing()` flag prevents React Strict Mode's
 * double-mount from destroying the singleton during initialization.
 *
 * ## Key Constraints
 *
 * - Must use the 'js' (js_of_ocaml) backend; the 'wa' (WASM) backend crashes
 *   with `flags.ml` assertion failures.
 * - The iframe requires `allow-scripts` and `allow-same-origin` sandbox
 *   permissions for jsCoq to function.
 * - The worker page (`coq-worker.html`) contains manual patches for
 *   non-monotonic state IDs and a coqReady promise wrapper.
 * - `softResetCoqService()` should be used on component unmount to preserve
 *   the iframe; `resetCoqService()` is for full teardown only.
 *
 * @see public/coq-worker.html - The iframe host page with jsCoq patches
 * @see src/hooks/useCoqSession.ts - React hook that wraps this service
 * @see src/lib/coq/coq-parser.ts - Statement parsing used by execute methods
 */
'use client';

import type { CoqGoal, VerificationResult, CoqWorkerStatus } from './types';
import { checkForbiddenTactics, isProofComplete } from './verifier';
import { parseStatements, isProofStart, parseGoalData } from './coq-parser';

/* ============================================================================
 * Callback Interface
 * ============================================================================
 * Consumers (typically React hooks) register these callbacks to receive
 * real-time updates about Coq's state, goals, errors, and execution progress.
 * ========================================================================= */

/**
 * Callbacks that consumers can register to receive updates from CoqService.
 * All callbacks are optional; the service operates correctly without any.
 * These are typically set by the `useCoqSession` hook.
 */
export interface CoqServiceCallbacks {
  /** Fired when the Coq worker transitions between states (idle, loading, ready, busy, error) */
  onStatusChange?: (status: CoqWorkerStatus) => void;

  /** Fired when jsCoq reports updated proof goals (e.g., after executing a tactic) */
  onGoalsUpdate?: (goals: CoqGoal[]) => void;

  /** Fired for informational, error, warning, notice, or success messages from Coq */
  onMessage?: (message: { type: 'info' | 'error' | 'warning' | 'notice' | 'success'; content: string }) => void;

  /** Fired on critical errors (initialization failures, execution crashes) */
  onError?: (error: string) => void;

  /** Fired once when jsCoq is fully initialized and ready to accept commands */
  onReady?: () => void;

  /** Fired during executeAll to report how many statements have been processed out of the total */
  onExecutionProgress?: (executed: number, total: number) => void;

  /**
   * Fired after each execute/undo operation with the character offset in the
   * source code up to which statements have been successfully executed.
   * Used by the editor to highlight the "verified" region.
   */
  onPositionChange?: (charOffset: number) => void;
}

/* ============================================================================
 * CoqService Class
 * ============================================================================
 * The main service class that manages the iframe lifecycle, command dispatch,
 * statement tracking, and proof verification.
 * ========================================================================= */

/**
 * CoqService - Iframe-isolated jsCoq integration.
 *
 * Runs jsCoq inside a hidden iframe to completely isolate it from the
 * Next.js environment. Communicates via postMessage IPC.
 *
 * Running jsCoq directly in the Next.js page causes stm.ml assertion failures
 * due to state machine conflicts. The iframe approach gives jsCoq a clean
 * browser context that avoids these issues.
 *
 * @example
 * ```ts
 * const service = getCoqService({ onGoalsUpdate: (goals) => setGoals(goals) });
 * await service.initialize();
 * service.setCode("Theorem test : True. Proof. exact I. Qed.");
 * const result = await service.verify("", userCode);
 * ```
 */
export class CoqService {
  /** Current status of the Coq worker (idle -> loading -> ready <-> busy | error) */
  private status: CoqWorkerStatus = 'idle';

  /** Registered consumer callbacks for state change notifications */
  private callbacks: CoqServiceCallbacks;

  /** Reference to the hidden iframe DOM element hosting jsCoq */
  private iframe: HTMLIFrameElement | null = null;

  /** The full Coq source code currently loaded in the editor/iframe */
  private currentCode: string = '';

  /**
   * Ordered list of Coq statements (sentences) that have been successfully
   * executed so far. Used to track the "cursor position" in the proof and
   * to compute which statement to execute/undo next.
   */
  private executedStatements: string[] = [];

  /** Whether any executed statement so far is a `Proof` command */
  private proofStarted: boolean = false;

  /**
   * Cached promise for the initialization sequence. If non-null, a subsequent
   * `initialize()` call will await this existing promise rather than creating
   * a new iframe. This prevents duplicate initializations.
   */
  private initPromise: Promise<void> | null = null;

  /** The most recent set of proof goals received from jsCoq */
  private currentGoals: CoqGoal[] = [];

  /** The most recent execution error message, used during verification */
  private executionError: string | null = null;

  /**
   * Flag indicating that the code in the iframe is out of sync with
   * `this.currentCode`. The `ensureCodeSynced()` method will resend the code
   * before executing statements.
   */
  private codeSyncPending: boolean = false;

  /**
   * Monotonically increasing sequence number for code sync operations.
   * When a sync completes, we only clear `codeSyncPending` if the sequence
   * number matches, preventing stale completions from clearing the flag
   * when newer code changes are pending.
   */
  private codeSyncSeq: number = 0;

  /** Auto-incrementing ID for postMessage commands, used to match responses */
  private messageId = 0;

  /**
   * Map of pending command IDs to their Promise resolve/reject handlers and
   * timeout timers. When a response arrives from the iframe, we look up the
   * ID here and settle the corresponding promise.
   */
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  private pendingMessages = new Map<number, { resolve: (data: any) => void; reject: (err: Error) => void; timeout: ReturnType<typeof setTimeout> }>();

  /** Reference to the global message event handler, stored for cleanup on destroy */
  private messageHandler: ((event: MessageEvent) => void) | null = null;

  /** Timer handle for the 60-second initialization timeout */
  private initTimeout: ReturnType<typeof setTimeout> | null = null;

  /**
   * Array of resolve callbacks from `waitForGoals()` promises. When a
   * `coq-goals` message arrives, all waiting resolvers are called.
   * This is used during `verify()` to wait for the final goal state.
   */
  private goalResolvers: Array<() => void> = [];

  /** Timer handle for the `waitForGoals()` timeout, stored for cleanup */
  private waitForGoalsTimer: ReturnType<typeof setTimeout> | null = null;

  /**
   * Creates a new CoqService instance.
   * @param callbacks - Optional callbacks for receiving state updates
   */
  constructor(callbacks: CoqServiceCallbacks = {}) {
    this.callbacks = callbacks;
  }

  /**
   * Replaces all registered callbacks. Called when a React component remounts
   * and needs to re-register its callbacks with the existing singleton.
   * @param callbacks - New set of callbacks to use
   */
  updateCallbacks(callbacks: CoqServiceCallbacks): void {
    this.callbacks = callbacks;
  }

  /**
   * Internal status setter that also notifies consumers via the onStatusChange callback.
   * @param status - The new worker status
   */
  private setStatus(status: CoqWorkerStatus): void {
    this.status = status;
    this.callbacks.onStatusChange?.(status);
  }

  /**
   * Returns the current status of the Coq worker.
   * @returns The current CoqWorkerStatus
   */
  getStatus(): CoqWorkerStatus {
    return this.status;
  }

  /* --------------------------------------------------------------------------
   * Initialization
   * --------------------------------------------------------------------------
   * The initialization flow is: initialize() -> doInitialize() -> createIframe()
   * The initPromise ensures only one initialization runs at a time. If a second
   * call comes in while initializing, it awaits the same promise.
   * ---------------------------------------------------------------------- */

  /**
   * Initializes the Coq runtime by creating the hidden iframe if not already
   * done. Safe to call multiple times -- subsequent calls await the existing
   * init promise and re-fire the onReady callback for remounted consumers.
   *
   * The re-notification on subsequent calls is critical: when a user navigates
   * away and back, the React component remounts with new callbacks. The iframe
   * is already ready, but the new component needs to know that.
   *
   * @throws Error if jsCoq fails to initialize within 60 seconds or encounters
   *         a fatal error during startup
   */
  async initialize(): Promise<void> {
    if (this.initPromise) {
      await this.initPromise;
      // Re-notify callbacks -- the consumer may have been remounted
      // (e.g. navigated away and back) and needs the ready signal.
      if (this.iframe) {
        this.setStatus('ready');
        this.callbacks.onReady?.();
      }
      return;
    }

    this.initPromise = this.doInitialize();
    return this.initPromise;
  }

  /**
   * Internal initialization logic. Creates the iframe and waits for the
   * `coq-ready` postMessage from the worker page.
   *
   * If initialization fails, `initPromise` is cleared so that a future
   * `initialize()` call can retry from scratch rather than being stuck
   * with a rejected promise.
   */
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

      await this.createIframe();

      this.setStatus('ready');
      this.callbacks.onReady?.();
      this.callbacks.onMessage?.({ type: 'info', content: 'Coq runtime initialized' });
    } catch (error) {
      // Clear initPromise so future initialize() calls can retry
      this.initPromise = null;
      this.setStatus('error');
      const errorMsg = error instanceof Error ? error.message : 'Failed to initialize Coq runtime';
      this.callbacks.onError?.(errorMsg);
      this.callbacks.onMessage?.({ type: 'error', content: errorMsg });
      throw error;
    }
  }

  /* --------------------------------------------------------------------------
   * Iframe Creation and Message Handling
   * --------------------------------------------------------------------------
   * The iframe is the isolation boundary between Next.js and jsCoq. The
   * message handler processes all postMessage events from the iframe:
   *   - coq-ready: initialization complete
   *   - coq-error: initialization failure
   *   - coq-goals: proof goal updates
   *   - coq-exec-error / coq-log-error: execution errors
   *   - coq-added-axiom: Admitted detection
   *   - coq-result: command response (matched by ID)
   *   - coq-pong: keepalive response (matched by ID)
   * ---------------------------------------------------------------------- */

  /**
   * Creates the hidden iframe, attaches the postMessage handler, and waits
   * for the `coq-ready` signal from the worker page.
   *
   * @returns Promise that resolves when jsCoq is ready, or rejects on error/timeout
   */
  private createIframe(): Promise<void> {
    return new Promise((resolve, reject) => {
      // Clean up any existing iframe from a previous failed attempt
      if (this.iframe) {
        this.iframe.remove();
        this.iframe = null;
      }

      // Guard against double resolve/reject after the init promise settles.
      // This is necessary because both the timeout and the message handler
      // can independently trigger rejection.
      let initSettled = false;
      const safeResolve = () => { if (!initSettled) { initSettled = true; resolve(); } };
      const safeReject = (err: Error) => { if (!initSettled) { initSettled = true; reject(err); } };

      // Set up the global message handler BEFORE creating the iframe to ensure
      // we don't miss the coq-ready event if the iframe initializes very quickly
      this.messageHandler = (event: MessageEvent) => {
        // Security: only accept messages from our own origin and our specific iframe
        if (event.origin !== window.location.origin) return;
        if (this.iframe && event.source !== this.iframe.contentWindow) return;
        const data = event.data;
        // All jsCoq messages are prefixed with 'coq-' to distinguish them from
        // any other postMessage traffic on the page
        if (!data?.type?.startsWith('coq-')) return;

        switch (data.type) {
          case 'coq-ready':
            // jsCoq has finished loading and is ready to accept commands
            if (this.initTimeout) {
              clearTimeout(this.initTimeout);
              this.initTimeout = null;
            }
            safeResolve();
            break;

          case 'coq-error':
            // jsCoq encountered a fatal error during initialization
            if (this.initTimeout) {
              clearTimeout(this.initTimeout);
              this.initTimeout = null;
            }
            safeReject(new Error(data.error));
            break;

          case 'coq-goals':
            // jsCoq is reporting updated proof goals (after a tactic executes)
            this.handleGoalInfo(data.goals);
            break;

          case 'coq-exec-error':
            // A statement execution failed (e.g., tactic doesn't apply)
            this.executionError = data.error;
            this.callbacks.onMessage?.({ type: 'error', content: data.error });
            break;

          case 'coq-log-error':
            // A less severe error logged by jsCoq (not displayed immediately,
            // but captured for verification result reporting)
            this.executionError = data.error;
            break;

          case 'coq-added-axiom':
            // jsCoq detected that an axiom was added (typically from Admitted),
            // meaning the proof is not actually complete
            this.callbacks.onMessage?.({ type: 'warning', content: 'Proof contains an unproven axiom (Admitted). Complete the proof to submit.' });
            break;

          case 'coq-result': {
            // Response to a sendCommand() call, matched by ID
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
            // Response to a ping/keepalive command, also matched by ID
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

      // Create the hidden iframe pointing to the jsCoq worker page.
      // The cache-busting query parameter ensures we always get a fresh page
      // after deployments. The iframe is positioned offscreen with zero opacity
      // but non-zero dimensions (jsCoq needs a real rendering context).
      const iframe = document.createElement('iframe');
      iframe.src = `/coq-worker.html?v=${Date.now()}`;
      iframe.sandbox.add('allow-scripts', 'allow-same-origin');
      iframe.style.cssText = 'position: fixed; left: 0; top: 0; width: 800px; height: 600px; opacity: 0; pointer-events: none; z-index: -9999; border: none;';
      document.body.appendChild(iframe);
      this.iframe = iframe;

      // 60-second timeout for initialization. jsCoq typically loads in 5-10s,
      // but slow networks or cold caches can take longer. If we timeout,
      // we clean up the half-initialized iframe to avoid dangling resources.
      this.initTimeout = setTimeout(() => {
        this.initTimeout = null;
        if (this.status === 'loading') {
          if (this.iframe) {
            this.iframe.remove();
            this.iframe = null;
          }
          if (this.messageHandler) {
            window.removeEventListener('message', this.messageHandler);
            this.messageHandler = null;
          }
          safeReject(new Error('Coq initialization timeout (60s)'));
        }
      }, 60000);
    });
  }

  /* --------------------------------------------------------------------------
   * Command Dispatch (postMessage IPC)
   * --------------------------------------------------------------------------
   * All commands to jsCoq go through sendCommand(), which assigns a unique ID,
   * posts the message to the iframe, and returns a promise that resolves when
   * the iframe responds with a matching coq-result message. Each command has
   * a 30-second timeout to prevent hanging promises.
   * ---------------------------------------------------------------------- */

  /**
   * Sends a command to the jsCoq iframe and waits for the result.
   *
   * Commands are dispatched via `postMessage` with a unique `id` field.
   * The iframe's message handler in `coq-worker.html` processes the command
   * and sends back a `coq-result` message with the same `id`.
   *
   * @param cmd - The command name (e.g., 'exec-next', 'exec-prev', 'reset', 'set-code')
   * @param args - Additional arguments to pass with the command
   * @returns Promise resolving to the response data from the iframe
   * @throws Error if the iframe is not available or the command times out (30s)
   */
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  private sendCommand(cmd: string, args: Record<string, unknown> = {}): Promise<any> {
    return new Promise((resolve, reject) => {
      if (!this.iframe?.contentWindow) {
        reject(new Error('Iframe not available'));
        return;
      }

      const id = ++this.messageId;

      // 30-second timeout prevents commands from hanging indefinitely
      // if jsCoq becomes unresponsive
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

  /* --------------------------------------------------------------------------
   * Goal Handling
   * --------------------------------------------------------------------------
   * Goals are the "proof obligations" that Coq reports after each tactic.
   * They arrive asynchronously via postMessage and are distributed to:
   * 1. The currentGoals cache (for verification checks)
   * 2. The onGoalsUpdate callback (for UI rendering)
   * 3. Any pending waitForGoals() promises (used during verify())
   * ---------------------------------------------------------------------- */

  /**
   * Processes raw goal data from the jsCoq iframe, parses it into typed
   * CoqGoal objects, caches them, notifies consumers, and resolves any
   * pending `waitForGoals()` promises.
   *
   * @param goalData - Raw goal data from jsCoq's postMessage
   */
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  private handleGoalInfo(goalData: any): void {
    const goals = parseGoalData(goalData);
    this.currentGoals = goals;
    this.callbacks.onGoalsUpdate?.(goals);

    // Resolve any promises that are waiting for goal updates.
    // This is used by verify() to wait for the final goal state after
    // executeAll() completes, since goals arrive asynchronously.
    const resolvers = this.goalResolvers;
    this.goalResolvers = [];
    resolvers.forEach(r => r());
  }

  /**
   * Returns a promise that resolves when the next goal update arrives,
   * or when the timeout expires (whichever comes first).
   *
   * This is essential during `verify()`: after `executeAll()` finishes,
   * the final goal state may not have arrived yet because it comes via
   * a separate postMessage. We wait briefly (500ms) for it.
   *
   * @param timeoutMs - Maximum time to wait for a goal update
   * @returns Promise that resolves when goals arrive or timeout expires
   */
  private waitForGoals(timeoutMs: number): Promise<void> {
    return new Promise(resolve => {
      const timer = setTimeout(() => {
        this.waitForGoalsTimer = null;
        // Remove our resolver from the array since we're resolving via timeout
        this.goalResolvers = this.goalResolvers.filter(r => r !== wrappedResolve);
        resolve();
      }, timeoutMs);
      this.waitForGoalsTimer = timer;
      const wrappedResolve = () => {
        clearTimeout(timer);
        this.waitForGoalsTimer = null;
        resolve();
      };
      this.goalResolvers.push(wrappedResolve);
    });
  }

  /* --------------------------------------------------------------------------
   * Code Synchronization
   * --------------------------------------------------------------------------
   * The editor's code and the iframe's code can get out of sync because
   * setCode() is called frequently (on every keystroke) but the postMessage
   * round-trip is asynchronous. The codeSyncPending flag and codeSyncSeq
   * counter ensure that we always send the latest code before executing.
   * ---------------------------------------------------------------------- */

  /**
   * Updates the current code and asynchronously syncs it to the iframe.
   * Called on every editor change. Uses a sequence number to prevent
   * stale completions from clearing the sync-pending flag.
   *
   * @param code - The full Coq source code from the editor
   */
  setCode(code: string): void {
    this.currentCode = code;
    this.codeSyncPending = true;
    const seq = ++this.codeSyncSeq;
    this.sendCommand('set-code', { code })
      .then(() => { if (seq === this.codeSyncSeq) this.codeSyncPending = false; })
      .catch(() => { /* codeSyncPending stays true; ensureCodeSynced will retry */ });
  }

  /**
   * Ensures the iframe has the latest code before executing statements.
   * If a sync is pending (setCode was called but hasn't completed),
   * this performs a blocking sync.
   */
  private async ensureCodeSynced(): Promise<void> {
    if (this.codeSyncPending) {
      await this.sendCommand('set-code', { code: this.currentCode });
      this.codeSyncPending = false;
    }
  }

  /**
   * Returns the current code string held by the service.
   * @returns The full Coq source code
   */
  getCode(): string {
    return this.currentCode;
  }

  /**
   * Returns whether a `Proof` command has been executed in the current session.
   * @returns True if proof mode has been entered
   */
  isProofStarted(): boolean {
    return this.proofStarted;
  }

  /**
   * Returns the number of statements that have been successfully executed.
   * Used by diagnostics to determine the index of the next (failing) statement.
   * @returns Count of executed statements
   */
  getExecutedCount(): number {
    return this.executedStatements.length;
  }

  /* --------------------------------------------------------------------------
   * Position Tracking
   * --------------------------------------------------------------------------
   * The "executed offset" is the character position in the source code up to
   * which all statements have been successfully executed. This is used by the
   * editor to highlight the verified region with a green background.
   * ---------------------------------------------------------------------- */

  /**
   * Computes the character offset in `currentCode` up to which statements
   * have been executed. Walks through the executed statements and finds
   * each one's position in the source code sequentially.
   *
   * @returns Character offset marking the end of the last executed statement
   */
  private computeExecutedOffset(): number {
    if (this.executedStatements.length === 0) return 0;
    let offset = 0;
    const code = this.currentCode;
    for (const stmt of this.executedStatements) {
      // Find each statement starting from after the previous one.
      // This handles cases where the same statement text appears multiple
      // times in the code (e.g., multiple `intros.` lines).
      const idx = code.indexOf(stmt, offset);
      if (idx === -1) break;
      offset = idx + stmt.length;
    }
    return offset;
  }

  /**
   * Fires the onPositionChange callback with the current executed offset.
   * Called after every execute/undo operation.
   */
  private firePositionChange(): void {
    this.callbacks.onPositionChange?.(this.computeExecutedOffset());
  }

  /* --------------------------------------------------------------------------
   * Statement Execution
   * --------------------------------------------------------------------------
   * These methods step through Coq statements one at a time (forward/backward)
   * or execute all at once. They maintain the executedStatements array and
   * proofStarted flag in sync with the iframe's state.
   * ---------------------------------------------------------------------- */

  /**
   * Executes the next Coq statement in the source code.
   *
   * Sends an `exec-next` command to the iframe, then updates the local
   * tracking state (executedStatements, proofStarted) to match. The statement
   * list is parsed from the current code and indexed by the count of
   * already-executed statements.
   *
   * @throws Error if Coq is not initialized or not in the 'ready' state
   */
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

      // `hasMore !== false` means a statement was actually executed.
      // Track it locally so we know what to undo and where the cursor is.
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

  /**
   * Undoes the last executed Coq statement (steps backward).
   *
   * Sends an `exec-prev` command to the iframe and removes the last entry
   * from executedStatements. The proofStarted flag is recomputed from
   * scratch over the remaining statements to handle the case where the
   * undone statement was the `Proof` command itself.
   *
   * @throws Error if Coq is not initialized or not in the 'ready' state
   */
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

      // Recompute proofStarted from remaining executed statements.
      // Simply checking the popped statement is insufficient because
      // the Proof command might have been several steps ago.
      this.proofStarted = this.executedStatements.some(s => isProofStart(s));

      this.setStatus('ready');
      this.firePositionChange();
    } catch (error) {
      this.setStatus('error');
      this.callbacks.onError?.(error instanceof Error ? error.message : 'Undo failed');
      throw error;
    }
  }

  /**
   * Executes all remaining Coq statements in the source code at once.
   *
   * Sends an `exec-all` command to the iframe, which processes all statements
   * and returns the count of successfully processed ones and any errors.
   * This is the primary method used by `verify()`.
   *
   * @returns Object with optional `stoppedAt` (error location) and `error` (message)
   * @throws Error if Coq is not initialized or not in the 'ready' state
   */
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

      // Update local tracking to reflect exactly what was processed.
      // If execution stopped partway due to an error, we only track
      // the statements that actually succeeded.
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

  /**
   * Executes or undoes statements to reach a specific character offset in
   * the source code. Used for "execute to cursor" functionality.
   *
   * Determines the target statement index from the character offset, then
   * steps forward or backward as needed. If an error occurs mid-way, the
   * service recovers to 'ready' state at the point where it stopped.
   *
   * @param charOffset - Target character position in the source code
   * @throws Error if Coq is not initialized or not in the 'ready' state
   */
  async executeToPosition(charOffset: number): Promise<void> {
    if (!this.iframe) {
      throw new Error('Coq not initialized');
    }

    if (this.status !== 'ready') {
      throw new Error('Coq is not ready');
    }

    await this.ensureCodeSynced();
    const statements = parseStatements(this.currentCode);

    // Determine how many statements fall within the target character offset
    // by walking through statements and accumulating their positions
    let targetIndex = 0;
    let currentOffset = 0;
    for (let i = 0; i < statements.length; i++) {
      const idx = this.currentCode.indexOf(statements[i], currentOffset);
      if (idx === -1) break;
      currentOffset = idx + statements[i].length;
      if (currentOffset >= charOffset) {
        targetIndex = i + 1;
        break;
      }
      targetIndex = i + 1;
    }

    const currentCount = this.executedStatements.length;

    try {
      // Step forward or backward to reach the target position
      if (targetIndex > currentCount) {
        for (let i = currentCount; i < targetIndex; i++) {
          await this.executeNext();
        }
      } else if (targetIndex < currentCount) {
        for (let i = currentCount; i > targetIndex; i--) {
          await this.executePrev();
        }
      }
    } catch (error) {
      // executeNext/executePrev set status to 'error' before throwing;
      // recover to 'ready' so the user can continue stepping from where we stopped
      if (this.getStatus() !== 'ready') {
        this.setStatus('ready');
      }
      throw error;
    }
  }

  /* --------------------------------------------------------------------------
   * Reset
   * ---------------------------------------------------------------------- */

  /**
   * Resets the Coq state machine to its initial state, clearing all executed
   * statements, goals, and errors. The iframe itself is preserved.
   *
   * This is used by `verify()` before running a new verification, and by
   * `softResetCoqService()` on component unmount.
   *
   * @throws Error if the reset command fails
   */
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

  /* --------------------------------------------------------------------------
   * Proof Verification
   * --------------------------------------------------------------------------
   * The verify() method is the high-level API used by ProblemSolver to check
   * whether a user's proof is correct. It:
   * 1. Checks for forbidden tactics (e.g., admit, Admitted)
   * 2. Resets the Coq state
   * 3. Concatenates prelude + user code
   * 4. Executes all statements
   * 5. Waits for final goals
   * 6. Checks completion criteria (no goals + Qed/Defined terminator + no errors)
   * ---------------------------------------------------------------------- */

  /**
   * Verifies a user's Coq proof against a problem's prelude.
   *
   * This is the main entry point for proof checking. It performs the
   * following steps:
   * 1. Checks for forbidden tactics (admit, Admitted, etc.) in user code
   * 2. Resets the Coq state machine to a clean slate
   * 3. Concatenates the problem's prelude with the user's code
   * 4. Executes all statements through jsCoq
   * 5. Waits briefly for the final goal state to propagate
   * 6. Determines if the proof is complete (no remaining goals, a Qed/Defined
   *    terminator exists, and no execution errors occurred)
   *
   * @param prelude - Problem setup code (imports, helper lemmas, theorem statement)
   * @param userCode - The user's proof attempt
   * @param forbiddenTactics - Tactics that are not allowed (default: ['admit', 'Admitted'])
   * @returns VerificationResult with success status, remaining goals, and any errors
   */
  async verify(
    prelude: string,
    userCode: string,
    forbiddenTactics: string[] = ['admit', 'Admitted']
  ): Promise<VerificationResult> {
    // Step 1: Check for forbidden tactics before even running Coq.
    // This is a fast client-side check that avoids unnecessary execution.
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

    // Step 2: Reset Coq and set up the full code
    await this.reset();
    this.executionError = null;
    const fullCode = `${prelude}\n\n${userCode}`;
    this.currentCode = fullCode;

    // Set code in the iframe and clear sync flag so executeAll's
    // ensureCodeSynced() doesn't re-sync with user-typed code.
    // This prevents a race condition where the editor's code (just the user
    // portion) overwrites the full prelude+user code we just set.
    await this.sendCommand('set-code', { code: fullCode });
    this.codeSyncPending = false;

    try {
      // Step 3: Execute all statements through jsCoq
      const execResult = await this.executeAll();

      // Step 4: Wait for goals to propagate via postMessage.
      // The 500ms timeout is a balance between responsiveness and reliability --
      // goals usually arrive within 50-100ms but can be delayed under load.
      await this.waitForGoals(500);

      // Step 5: Determine completion status
      const goals = this.currentGoals;
      const hasTerminator = isProofComplete(userCode);
      const errors: string[] = [];

      if (execResult.stoppedAt) {
        errors.push(execResult.error || `Execution stopped at: ${execResult.stoppedAt}`);
      }

      if (this.executionError && !errors.includes(this.executionError)) {
        errors.push(this.executionError);
      }

      // A proof is complete only when ALL three conditions are met:
      // 1. No remaining proof goals (all obligations discharged)
      // 2. A Qed or Defined terminator exists (proof is sealed)
      // 3. No execution errors occurred
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
      // Recover service to ready state so subsequent actions work.
      // Without this recovery, the service would be stuck in 'error' or 'busy'
      // and the user would need to reload the page.
      if (this.status === 'error' || this.status === 'busy') {
        this.setStatus('ready');
      }
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

  /* --------------------------------------------------------------------------
   * Cleanup / Teardown
   * ---------------------------------------------------------------------- */

  /**
   * Fully destroys the CoqService instance, removing the iframe, cleaning up
   * all event listeners, canceling pending operations, and resetting all state.
   *
   * After calling destroy(), the service cannot be used again. A new instance
   * must be created via `getCoqService()`.
   *
   * This method sets status directly (not via setStatus) to avoid firing
   * callbacks on a service that is being torn down, which could cause
   * React state updates on unmounted components.
   */
  destroy(): void {
    // Clear init timeout to prevent late rejection
    if (this.initTimeout) {
      clearTimeout(this.initTimeout);
      this.initTimeout = null;
    }

    // Remove the global message event listener
    if (this.messageHandler) {
      window.removeEventListener('message', this.messageHandler);
      this.messageHandler = null;
    }

    // Remove the iframe from the DOM (this also kills any web workers
    // and JavaScript execution contexts inside it)
    if (this.iframe) {
      this.iframe.remove();
      this.iframe = null;
    }

    // Reject all pending command promises to prevent memory leaks
    // and dangling await calls
    this.pendingMessages.forEach((pending) => {
      clearTimeout(pending.timeout);
      pending.reject(new Error('Service destroyed'));
    });
    this.pendingMessages.clear();

    // Clear waitForGoals timer to prevent callbacks after destroy
    if (this.waitForGoalsTimer) {
      clearTimeout(this.waitForGoalsTimer);
      this.waitForGoalsTimer = null;
    }

    // Reset all internal state
    this.executedStatements = [];
    this.proofStarted = false;
    this.currentCode = '';
    this.currentGoals = [];
    this.executionError = null;
    this.codeSyncPending = false;
    this.goalResolvers = [];
    this.initPromise = null;
    // Set status directly to avoid firing callbacks on a destroyed service
    this.status = 'idle';
  }
}

/* ==============================================================================
 * Singleton Management
 * ==============================================================================
 * The CoqService singleton pattern ensures that the expensive iframe
 * initialization (~5-10 seconds) is only done once and persists across React
 * component mounts/unmounts and page navigations.
 *
 * Three functions manage the singleton lifecycle:
 * - getCoqService(): Creates or retrieves the singleton, updating callbacks
 * - resetCoqService(): Full teardown (use sparingly)
 * - softResetCoqService(): Clears Coq state without destroying iframe (preferred)
 * - setInitializing(): Prevents React Strict Mode double-mount from destroying
 *   the singleton during the async initialization window
 * =========================================================================== */

/** Module-level singleton instance -- persists across React remounts */
let serviceInstance: CoqService | null = null;

/**
 * Guard flag to prevent `resetCoqService()` from destroying the singleton
 * during the asynchronous initialization window. React Strict Mode in
 * development calls useEffect cleanup (which calls resetCoqService) immediately
 * after the first mount, before the second mount's initialization completes.
 * Without this guard, the iframe would be destroyed mid-initialization.
 */
let isInitializing = false;

/**
 * Returns the CoqService singleton, creating it if necessary.
 * If the singleton already exists, updates its callbacks to the provided ones.
 *
 * @param callbacks - Callbacks for receiving Coq state updates
 * @returns The CoqService singleton instance
 */
export function getCoqService(callbacks: CoqServiceCallbacks = {}): CoqService {
  if (!serviceInstance) {
    serviceInstance = new CoqService(callbacks);
  } else if (Object.keys(callbacks).length > 0) {
    serviceInstance.updateCallbacks(callbacks);
  }
  return serviceInstance;
}

/**
 * Fully destroys the CoqService singleton, including the iframe.
 * Use this only when the entire Coq subsystem needs to be torn down
 * (e.g., the app is being unloaded). For normal navigation, prefer
 * `softResetCoqService()`.
 *
 * No-ops if the service is currently initializing (protected by the
 * `isInitializing` flag to handle React Strict Mode double-mount).
 */
export function resetCoqService(): void {
  // Don't destroy during initialization (React Strict Mode causes double-mount)
  if (isInitializing) {
    return;
  }
  serviceInstance?.destroy();
  serviceInstance = null;
}

/**
 * Soft reset: clears Coq execution state (goals, executed statements, errors)
 * without destroying the iframe or the singleton instance.
 *
 * This is the preferred cleanup method on component unmount. It preserves
 * the expensive iframe initialization across page navigations, so the next
 * page that uses Coq gets instant readiness instead of a 5-10 second wait.
 *
 * If the soft reset fails (e.g., the iframe is in a bad state), it silently
 * catches the error. The next `initialize()` call will handle recovery.
 */
export async function softResetCoqService(): Promise<void> {
  if (isInitializing || !serviceInstance) return;
  try {
    await serviceInstance.reset();
  } catch {
    // If soft reset fails, the service remains usable -- next initialize() will handle it
  }
}

/**
 * Sets the initializing guard flag. Must be set to `true` before calling
 * `initialize()` and set to `false` after it completes. This prevents
 * React Strict Mode's cleanup function from destroying the singleton
 * while it's still being initialized.
 *
 * @param value - Whether initialization is in progress
 */
export function setInitializing(value: boolean): void {
  isInitializing = value;
}
