/**
 * @module coq/index
 *
 * Public API barrel file for the Coq subsystem.
 *
 * Re-exports the core types, verification utilities, and the CoqService
 * singleton management functions. This is the primary import point for
 * consumers outside the `src/lib/coq/` directory.
 *
 * ## What's Exported
 *
 * From `types.ts`:
 * - `CoqGoal`, `CoqHypothesis` - Proof goal structures
 * - `CoqMessage` - Unified message type
 * - `VerificationResult` - Proof verification result
 * - `CoqWorkerStatus` - Iframe lifecycle status
 *
 * From `verifier.ts`:
 * - `checkForbiddenTactics()` - Pre-execution forbidden tactic detection
 * - `isProofComplete()` - Post-execution proof terminator check
 *
 * From `CoqService.ts`:
 * - `CoqService` - The main service class
 * - `getCoqService()` - Singleton accessor
 * - `resetCoqService()` - Full singleton teardown
 * - `softResetCoqService()` - Lightweight state reset (preferred for navigation)
 * - `setInitializing()` - React Strict Mode double-mount guard
 *
 * ## What's NOT Exported Here
 *
 * The following modules have their own import paths because they are only
 * needed by specific consumers (the CodeMirror editor):
 * - `coq-syntax.ts` - CodeMirror language definition
 * - `coq-autocomplete.ts` - CodeMirror autocomplete extension
 * - `coq-hover.ts` - CodeMirror hover tooltip extension
 * - `coq-parser.ts` - Internal parser (used by CoqService, not external consumers)
 * - `tactic-suggester.ts` - Tactic suggestion engine (imported directly by components)
 * - `tactic-docs.ts` - Tactic documentation data
 * - `error-helper.ts` - Error message translation
 *
 * @see CoqService.ts - The central singleton managing the jsCoq iframe
 * @see types.ts - Core type definitions
 * @see verifier.ts - Verification utilities
 */
export * from './types';
export * from './verifier';
export { CoqService, getCoqService, resetCoqService, softResetCoqService, setInitializing } from './CoqService';
