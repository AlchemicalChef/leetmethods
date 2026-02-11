/**
 * @module types
 *
 * Core type definitions for the Coq subsystem.
 *
 * This module defines the shared types used across the entire Coq integration:
 * CoqService, verifier, parser, tactic suggester, and the Zustand stores.
 * These types form the contract between the jsCoq iframe layer and the
 * React UI layer.
 *
 * ## Canonical Definitions
 *
 * These types are the **canonical** (single source of truth) definitions.
 * The `coqStore` in `src/store/` imports and uses these types directly rather
 * than defining its own. This ensures consistency between the lib layer
 * (which must not import from store) and the store layer.
 *
 * ## Key Relationships
 *
 * - `CoqGoal` and `CoqHypothesis` are produced by `parseGoalData()` in
 *   `coq-parser.ts` and consumed by the GoalsPanel UI component.
 * - `CoqMessage` is produced by CoqService callbacks and consumed by the
 *   coqStore's message list.
 * - `VerificationResult` is produced by `CoqService.verify()` and consumed
 *   by ProblemSolver to determine proof completion.
 * - `CoqWorkerStatus` tracks the iframe lifecycle state and drives the
 *   CoqStatusBar loading/error indicators.
 *
 * @see CoqService.ts - Primary producer of these types
 * @see src/store/coqStore.ts - Primary consumer of these types
 * @see coq-parser.ts - Produces CoqGoal from raw jsCoq data
 */

/* ==============================================================================
 * Proof Goal Types
 * ==============================================================================
 * These types represent the structured proof state that Coq reports after
 * each tactic execution. A proof goal consists of hypotheses (the things
 * we know) and a conclusion (the thing we need to prove).
 * =========================================================================== */

/**
 * Represents a single proof goal (obligation) in the current Coq proof state.
 *
 * In Coq, after applying a tactic, there may be zero or more goals remaining.
 * Each goal has a list of hypotheses (assumptions in scope) and a conclusion
 * (the proposition to prove). Multiple goals arise from tactics like `split`
 * (which creates two subgoals) or `induction` (which creates base and
 * inductive cases).
 *
 * @example
 * ```
 * Goal 1:
 *   H : nat               <- hypothesis
 *   H0 : H > 0            <- hypothesis
 *   ========================
 *   H + 1 > 1             <- conclusion
 * ```
 */
export interface CoqGoal {
  /** Sequential goal number (1-indexed), used for display purposes */
  id: number;

  /** List of hypotheses (assumptions) available in this goal's context */
  hypotheses: CoqHypothesis[];

  /**
   * The proposition that needs to be proved.
   * This is a plain text string representation of the Coq term
   * (e.g., "forall n : nat, n + 0 = n").
   */
  conclusion: string;
}

/**
 * A single hypothesis (assumption) in a proof goal's context.
 *
 * Hypotheses are the "known facts" available to the prover. They come from:
 * - `intros` (introducing universal quantifiers and implications)
 * - `destruct`/`induction` (case analysis)
 * - `assert`/`pose` (adding intermediate lemmas)
 *
 * @example
 * ```
 * H : forall n : nat, n + 0 = n
 * ```
 * Here, name = "H" and type = "forall n : nat, n + 0 = n"
 */
export interface CoqHypothesis {
  /**
   * The hypothesis name (e.g., "H", "IHn", "x").
   * For grouped hypotheses like `x y : nat`, this will be "x, y".
   */
  name: string;

  /** The type of the hypothesis as a plain text string */
  type: string;
}

/* ==============================================================================
 * Message Types
 * ==============================================================================
 * Messages are informational, error, or warning outputs from Coq that should
 * be displayed to the user in the message panel.
 * =========================================================================== */

/**
 * Unified message type used by both the lib layer (CoqService callbacks)
 * and the store layer (coqStore message list).
 *
 * This is the canonical definition -- coqStore imports this type directly
 * rather than defining its own, ensuring type consistency across layers.
 */
export interface CoqMessage {
  /** The severity/category of the message */
  type: 'info' | 'error' | 'warning' | 'notice' | 'success';

  /** The message text content */
  content: string;

  /**
   * Timestamp of when the message was created. Set by `coqStore.addMessage()`
   * when the message is added to the store. Optional in the lib context
   * because CoqService doesn't set timestamps -- it just fires callbacks.
   */
  timestamp?: number;
}

/* ==============================================================================
 * Verification Result
 * ==============================================================================
 * The complete result of a proof verification attempt, returned by
 * CoqService.verify(). Contains everything the UI needs to display
 * verification feedback.
 * =========================================================================== */

/**
 * Complete result of a proof verification attempt.
 *
 * Produced by `CoqService.verify()` and consumed by the ProblemSolver
 * component to determine whether a proof is complete, display errors,
 * and update progress tracking.
 *
 * A proof is considered complete (`isComplete === true`) when ALL of:
 * 1. No remaining proof goals (`goals.length === 0`)
 * 2. The code contains a proof terminator (`Qed` or `Defined`)
 * 3. No execution errors occurred
 * 4. No forbidden tactics were used
 */
export interface VerificationResult {
  /** Whether the proof was successfully verified as complete */
  success: boolean;

  /** Remaining proof goals (empty if proof is complete) */
  goals: CoqGoal[];

  /** Error messages encountered during verification */
  errors: string[];

  /** Informational messages from the verification process */
  messages: CoqMessage[];

  /** Whether any forbidden tactics were detected in the user's code */
  hasForbiddenTactics: boolean;

  /** List of forbidden tactic names that were found in the code */
  forbiddenTacticsFound: string[];

  /**
   * Whether the proof is genuinely complete: zero goals, Qed/Defined present,
   * and no errors. This is the authoritative completion flag used by the
   * progress tracking system.
   */
  isComplete: boolean;
}

/* ==============================================================================
 * Worker Status
 * ==============================================================================
 * Tracks the lifecycle state of the jsCoq iframe worker. Used by the
 * CoqStatusBar component to show loading spinners and error indicators.
 * =========================================================================== */

/**
 * Lifecycle status of the Coq worker (jsCoq iframe).
 *
 * State transitions:
 * ```
 * idle -> loading -> ready <-> busy
 *                      |         |
 *                      v         v
 *                    error     error
 * ```
 *
 * - `idle`: Initial state before `initialize()` is called
 * - `loading`: The iframe is being created and jsCoq is loading (~5-10 seconds)
 * - `ready`: jsCoq is initialized and accepting commands
 * - `busy`: A command (execute, verify, reset) is in progress
 * - `error`: A fatal error occurred (initialization failure, command crash)
 */
export type CoqWorkerStatus = 'idle' | 'loading' | 'ready' | 'busy' | 'error';
