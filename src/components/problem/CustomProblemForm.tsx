/**
 * @module CustomProblemForm
 *
 * A multi-section form for creating and editing user-defined Coq proof problems.
 *
 * This component powers the /problems/custom/create page and the edit flow for
 * existing custom problems. It provides a structured form with four sections:
 *
 * 1. **Problem Metadata** -- Title, difficulty, category, tags, description
 * 2. **Coq Code** -- Prelude (imports), template (starting code), solution (reference proof)
 * 3. **Hints** -- Dynamic list of hints that can be added/removed
 * 4. **Verify & Save** -- Solution verification against jsCoq before saving
 *
 * Key design decisions:
 *
 * - **Solution verification is required before saving** (new problems only).
 *   The form dynamically imports CoqService to verify the solution actually
 *   compiles and proves the theorem. This prevents users from creating problems
 *   with broken solutions. Editing bypasses this requirement since the solution
 *   was already verified on creation.
 *
 * - **Dynamic CoqService import**: The verify flow uses `await import(...)` to
 *   load CoqService lazily, avoiding SSR issues (jsCoq requires browser APIs).
 *   After verification, `softResetCoqService()` is called to clean up the
 *   singleton state without destroying the iframe.
 *
 * - **Hint items use a local ID counter** to provide stable React keys even
 *   when hints are added/removed from the middle of the list. The counter is
 *   module-scoped (not per-instance) which is fine since only one form exists
 *   at a time.
 *
 * - **Field-level validation**: Title must be >= 3 chars, template is required,
 *   and solution must contain "Qed." (indicating a complete proof, not Admitted).
 *   Errors are cleared per-field as the user makes corrections.
 *
 * - **The verified flag resets** whenever any field changes, requiring
 *   re-verification. This ensures the solution is always tested against the
 *   current prelude and template state.
 *
 * @see {@link customProblemStore} for persistence of created problems
 * @see {@link CoqService} for the jsCoq verification bridge
 */
'use client';

import { useState, useCallback } from 'react';
import { Button } from '@/components/ui/button';
import { Card } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import {
  Select,
  SelectContent,
  SelectItem,
  SelectTrigger,
  SelectValue,
} from '@/components/ui/select';
import { Plus, Trash2, CheckCircle2, Loader2, AlertCircle } from 'lucide-react';
import type { Difficulty, Category } from '@/lib/problems/types';

/* ============================================================================
 * Types
 * ============================================================================ */

/**
 * Represents a single hint with a stable ID for React list rendering.
 * The ID is auto-incremented from a module-scoped counter.
 */
interface HintItem {
  /** Unique identifier for stable React keys */
  id: number;
  /** The hint text content */
  text: string;
}

/**
 * Form data structure for creating/editing a custom problem.
 * Maps directly to the fields stored in customProblemStore.
 */
interface CustomProblemFormData {
  /** Problem title (min 3 characters) */
  title: string;
  /** Difficulty level: easy, medium, or hard */
  difficulty: Difficulty;
  /** Problem category (logic, booleans, induction, etc.) */
  category: Category;
  /** Comma-separated tag string (split on save) */
  tags: string;
  /** Problem description (supports markdown-like formatting) */
  description: string;
  /** Read-only prelude code (imports/definitions prepended to user code) */
  prelude: string;
  /** Starting template code shown to the solver (should end with Admitted.) */
  template: string;
  /** Reference solution code (must contain Qed. and pass verification) */
  solution: string;
  /** Array of hint strings for progressive reveal */
  hints: string[];
}

/**
 * Props for the CustomProblemForm component.
 */
interface CustomProblemFormProps {
  /** Initial form data when editing an existing problem */
  initialData?: CustomProblemFormData;
  /** Called when the form is saved with valid, verified data */
  onSave: (data: CustomProblemFormData) => void;
  /** Called when the user cancels the form */
  onCancel: () => void;
  /** Whether this is editing an existing problem (skips verification requirement) */
  isEditing?: boolean;
}

/* ============================================================================
 * Default Data & Hint ID Counter
 * ============================================================================ */

/**
 * Default form values for a new custom problem.
 * The template uses Admitted. as a placeholder so the forbidden tactic
 * detector catches unmodified submissions.
 */
const defaultData: CustomProblemFormData = {
  title: '',
  difficulty: 'easy',
  category: 'logic',
  tags: '',
  description: '',
  prelude: '',
  template: 'Theorem my_theorem : True.\nProof.\n  (* Your proof here *)\nAdmitted.',
  solution: 'Theorem my_theorem : True.\nProof.\n  exact I.\nQed.',
  hints: [''],
};

/**
 * Module-scoped counter for generating unique hint item IDs.
 * Incremented each time a hint is created. Only one form instance
 * exists at a time so collisions are not a concern.
 */
let hintIdCounter = 0;

/**
 * Convert an array of hint strings into HintItem objects with unique IDs.
 *
 * @param hints - Array of hint text strings
 * @returns Array of HintItem objects with auto-incremented IDs
 */
function toHintItems(hints: string[]): HintItem[] {
  return hints.map((text) => ({ id: hintIdCounter++, text }));
}

/* ============================================================================
 * CustomProblemForm Component
 * ============================================================================ */

/**
 * Multi-section form for creating or editing a custom Coq proof problem.
 *
 * Includes metadata fields, Coq code editors (plain textareas), dynamic
 * hint management, solution verification via jsCoq, and save/cancel actions.
 *
 * @param props - See {@link CustomProblemFormProps}
 * @returns The multi-section form UI
 */
export function CustomProblemForm({ initialData, onSave, onCancel, isEditing = false }: CustomProblemFormProps) {
  /** Form data state -- initialized from initialData or defaults */
  const [data, setData] = useState<CustomProblemFormData>(initialData ?? defaultData);
  /** Hint items with stable IDs for list rendering */
  const [hintItems, setHintItems] = useState<HintItem[]>(() => toHintItems((initialData ?? defaultData).hints));
  /** Whether the solution has been successfully verified against jsCoq */
  const [verified, setVerified] = useState(false);
  /** Whether verification is currently in progress */
  const [verifying, setVerifying] = useState(false);
  /** Error message from the last verification attempt, if any */
  const [verifyError, setVerifyError] = useState<string | null>(null);
  /** Per-field validation error messages */
  const [errors, setErrors] = useState<Record<string, string>>({});

  /**
   * Update a single form field and reset verification status.
   * Any field change invalidates the previous verification because the
   * solution might no longer be correct with the changed prelude/template.
   * Also clears the validation error for the changed field.
   */
  const updateField = useCallback(<K extends keyof CustomProblemFormData>(key: K, value: CustomProblemFormData[K]) => {
    setData((prev) => ({ ...prev, [key]: value }));
    setVerified(false);
    setErrors((prev) => {
      const next = { ...prev };
      delete next[key];
      return next;
    });
  }, []);

  /**
   * Synchronize hint items back to the data.hints array.
   * Called after any hint add/update/remove operation to keep
   * the HintItem[] state and data.hints in sync.
   */
  const syncHints = (items: HintItem[]) => {
    setHintItems(items);
    setData((prev) => ({ ...prev, hints: items.map((h) => h.text) }));
  };

  /** Add a new empty hint to the end of the list */
  const addHint = () => {
    syncHints([...hintItems, { id: hintIdCounter++, text: '' }]);
  };

  /** Update the text of an existing hint at a specific index */
  const updateHint = (index: number, value: string) => {
    const updated = [...hintItems];
    updated[index] = { ...updated[index], text: value };
    syncHints(updated);
  };

  /** Remove a hint at a specific index */
  const removeHint = (index: number) => {
    syncHints(hintItems.filter((_, i) => i !== index));
  };

  /**
   * Validate form fields and return whether validation passed.
   * Sets error messages for fields that fail validation.
   *
   * @returns true if all validations pass, false otherwise
   */
  const validate = (): boolean => {
    const newErrors: Record<string, string> = {};
    if (data.title.trim().length < 3) {
      newErrors.title = 'Title must be at least 3 characters';
    }
    if (!data.template.trim()) {
      newErrors.template = 'Template is required';
    }
    // Solution must contain Qed. to ensure it's a complete proof (not Admitted)
    if (!data.solution.includes('Qed.')) {
      newErrors.solution = 'Solution must contain Qed.';
    }
    setErrors(newErrors);
    return Object.keys(newErrors).length === 0;
  };

  /**
   * Verify the solution against jsCoq to ensure it compiles and proves
   * the theorem without using forbidden tactics (admit, Admitted).
   *
   * Uses dynamic import to load CoqService lazily (avoids SSR issues).
   * After verification, performs a soft reset to clean up the singleton
   * state without destroying the iframe.
   */
  const handleVerify = async () => {
    if (!validate()) return;
    setVerifying(true);
    setVerifyError(null);

    try {
      // Dynamically import CoqService to avoid SSR issues with jsCoq
      const { getCoqService, softResetCoqService } = await import('@/lib/coq');
      // Get the existing singleton service (or create one if none exists)
      const service = getCoqService();
      await service.initialize();
      const result = await service.verify(data.prelude, data.solution, ['admit', 'Admitted']);
      // Clean up verification state from the singleton without destroying the iframe
      await softResetCoqService();
      if (result.success) {
        setVerified(true);
        setVerifyError(null);
      } else {
        setVerifyError(result.errors.join('; ') || 'Solution verification failed');
      }
    } catch (err) {
      setVerifyError(err instanceof Error ? err.message : 'Verification failed');
    } finally {
      setVerifying(false);
    }
  };

  /**
   * Save the problem if validation passes and solution is verified.
   * When editing, verification is not required (it was done on creation).
   */
  const handleSave = () => {
    if (!validate()) return;
    if (!verified && !isEditing) return;
    onSave(data);
  };

  return (
    <div className="space-y-8">
      {/* ================================================================
       * Section 1: Problem Metadata
       * ================================================================ */}
      <Card className="p-6">
        <h3 className="text-lg font-semibold mb-4">Problem Metadata</h3>
        <div className="space-y-4">
          {/* Title field (required, min 3 characters) */}
          <div>
            <label className="block text-sm font-medium mb-1">Title *</label>
            <input
              type="text"
              value={data.title}
              onChange={(e) => updateField('title', e.target.value)}
              className="w-full px-3 py-2 border rounded-md bg-background"
              placeholder="e.g., Prove Modus Ponens"
            />
            {errors.title && <p className="text-xs text-red-500 mt-1">{errors.title}</p>}
          </div>

          {/* Difficulty and Category dropdowns in a 2-column grid */}
          <div className="grid grid-cols-2 gap-4">
            <div>
              <label className="block text-sm font-medium mb-1">Difficulty</label>
              <Select value={data.difficulty} onValueChange={(v) => updateField('difficulty', v as Difficulty)}>
                <SelectTrigger>
                  <SelectValue />
                </SelectTrigger>
                <SelectContent>
                  <SelectItem value="easy">Easy</SelectItem>
                  <SelectItem value="medium">Medium</SelectItem>
                  <SelectItem value="hard">Hard</SelectItem>
                </SelectContent>
              </Select>
            </div>
            <div>
              <label className="block text-sm font-medium mb-1">Category</label>
              <Select value={data.category} onValueChange={(v) => updateField('category', v as Category)}>
                <SelectTrigger>
                  <SelectValue />
                </SelectTrigger>
                <SelectContent>
                  <SelectItem value="logic">Logic</SelectItem>
                  <SelectItem value="booleans">Booleans</SelectItem>
                  <SelectItem value="induction">Induction</SelectItem>
                  <SelectItem value="lists">Lists</SelectItem>
                  <SelectItem value="arithmetic">Arithmetic</SelectItem>
                  <SelectItem value="data-structures">Data Structures</SelectItem>
                  <SelectItem value="relations">Relations</SelectItem>
                </SelectContent>
              </Select>
            </div>
          </div>

          {/* Tags input (comma-separated, split on save) */}
          <div>
            <label className="block text-sm font-medium mb-1">Tags (comma-separated)</label>
            <input
              type="text"
              value={data.tags}
              onChange={(e) => updateField('tags', e.target.value)}
              className="w-full px-3 py-2 border rounded-md bg-background"
              placeholder="e.g., basic, implication"
            />
          </div>

          {/* Description textarea */}
          <div>
            <label className="block text-sm font-medium mb-1">Description</label>
            <textarea
              value={data.description}
              onChange={(e) => updateField('description', e.target.value)}
              className="w-full px-3 py-2 border rounded-md bg-background min-h-[100px]"
              placeholder="Describe the problem..."
            />
          </div>
        </div>
      </Card>

      {/* ================================================================
       * Section 2: Coq Code
       * ================================================================ */}
      <Card className="p-6">
        <h3 className="text-lg font-semibold mb-4">Coq Code</h3>
        <div className="space-y-4">
          {/* Prelude: read-only imports/definitions prepended before user code */}
          <div>
            <label className="block text-sm font-medium mb-1">Prelude (read-only imports)</label>
            <textarea
              value={data.prelude}
              onChange={(e) => updateField('prelude', e.target.value)}
              className="w-full px-3 py-2 border rounded-md bg-background font-mono text-sm min-h-[80px]"
              placeholder="Require Import Arith."
            />
          </div>

          {/* Template: the starting code shown to the solver */}
          <div>
            <label className="block text-sm font-medium mb-1">Template * (initial code for solver)</label>
            <textarea
              value={data.template}
              onChange={(e) => updateField('template', e.target.value)}
              className="w-full px-3 py-2 border rounded-md bg-background font-mono text-sm min-h-[120px]"
            />
            {errors.template && <p className="text-xs text-red-500 mt-1">{errors.template}</p>}
          </div>

          {/* Solution: the reference proof that must pass verification */}
          <div>
            <label className="block text-sm font-medium mb-1">Solution * (reference proof)</label>
            <textarea
              value={data.solution}
              onChange={(e) => updateField('solution', e.target.value)}
              className="w-full px-3 py-2 border rounded-md bg-background font-mono text-sm min-h-[120px]"
            />
            {errors.solution && <p className="text-xs text-red-500 mt-1">{errors.solution}</p>}
          </div>
        </div>
      </Card>

      {/* ================================================================
       * Section 3: Hints (dynamic list)
       * ================================================================ */}
      <Card className="p-6">
        <h3 className="text-lg font-semibold mb-4">Hints</h3>
        <div className="space-y-2">
          {/* Render each hint with its 1-based index, input field, and remove button */}
          {hintItems.map((hint, index) => (
            <div key={hint.id} className="flex items-center gap-2">
              <span className="text-xs text-muted-foreground w-6">{index + 1}.</span>
              <input
                type="text"
                value={hint.text}
                onChange={(e) => updateHint(index, e.target.value)}
                className="flex-1 px-3 py-2 border rounded-md bg-background text-sm"
                placeholder="Enter a hint..."
              />
              <Button variant="ghost" size="sm" onClick={() => removeHint(index)}>
                <Trash2 className="h-3 w-3" />
              </Button>
            </div>
          ))}
          {/* Button to add a new empty hint */}
          <Button variant="outline" size="sm" onClick={addHint}>
            <Plus className="h-3 w-3 mr-1" />
            Add Hint
          </Button>
        </div>
      </Card>

      {/* ================================================================
       * Section 4: Verification & Save
       * ================================================================ */}
      <Card className="p-6">
        <h3 className="text-lg font-semibold mb-4">Verify & Save</h3>
        <div className="space-y-3">
          {/* Verify button -- tests the solution against jsCoq */}
          <div className="flex items-center gap-3">
            <Button
              onClick={handleVerify}
              disabled={verifying}
              variant="outline"
            >
              {verifying ? (
                <Loader2 className="h-4 w-4 mr-1 animate-spin" />
              ) : verified ? (
                <CheckCircle2 className="h-4 w-4 mr-1 text-green-500" />
              ) : (
                <AlertCircle className="h-4 w-4 mr-1" />
              )}
              {verifying ? 'Verifying...' : verified ? 'Verified' : 'Test Solution'}
            </Button>
            {/* Success badge shown after verification passes */}
            {verified && (
              <Badge className="bg-green-100 text-green-800 dark:bg-green-900 dark:text-green-200">
                Solution passes
              </Badge>
            )}
          </div>
          {/* Verification error message */}
          {verifyError && (
            <p className="text-sm text-red-500">{verifyError}</p>
          )}
          {/* Save and Cancel buttons */}
          <div className="flex items-center gap-3 pt-2">
            <Button
              onClick={handleSave}
              disabled={!verified && !isEditing}
              className="bg-green-600 hover:bg-green-700"
            >
              {isEditing ? 'Save Changes' : 'Create Problem'}
            </Button>
            <Button variant="outline" onClick={onCancel}>
              Cancel
            </Button>
          </div>
          {/* Hint text when verification is required */}
          {!verified && !isEditing && (
            <p className="text-xs text-muted-foreground">Test the solution before saving</p>
          )}
        </div>
      </Card>
    </div>
  );
}
