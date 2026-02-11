/**
 * @module editorStore
 *
 * Persisted Zustand store for the Coq code editor state.
 *
 * This store manages the current editor content, tracks which problem is
 * active, and persists saved code across browser sessions. It enables the
 * user to navigate away from a problem and return later to find their
 * in-progress proof exactly as they left it.
 *
 * Persistence strategy:
 * - Only the `savedCodes` map is persisted to localStorage (via `partialize`).
 *   Ephemeral fields like `code`, `problemSlug`, and `isDirty` are not
 *   persisted because they represent the current editing session state,
 *   which is re-established when the user navigates to a problem page.
 * - Uses `safeStorage` to gracefully handle `QuotaExceededError`.
 *
 * Data flow:
 * 1. User navigates to a problem -> `loadCode(slug, template)` is called.
 * 2. If saved code exists for that slug, it's loaded; otherwise the
 *    problem's default template is used.
 * 3. As the user types, `setCode()` updates `code` and marks `isDirty`.
 * 4. On successful submission or explicit save, `saveCode()` persists
 *    the current code into `savedCodes`.
 * 5. `resetCode()` reverts to the template and removes the saved entry.
 *
 * The `isDirty` flag can be used by the UI to show unsaved-changes
 * indicators or prompt before navigation.
 */

import { create } from 'zustand';
import { persist } from 'zustand/middleware';
import { safeStorage } from '@/lib/safe-storage';

/* ─── Store Interface ───────────────────────────────────────────────────── */

interface EditorState {
  /** The current content of the code editor (live, potentially unsaved). */
  code: string;

  /**
   * The slug of the problem currently loaded in the editor, or null if no
   * problem is active. Used to associate saves with the correct problem.
   */
  problemSlug: string | null;

  /**
   * Whether the editor content has been modified since the last save or load.
   * Reset to false by `saveCode()`, `loadCode()`, and `resetCode()`.
   */
  isDirty: boolean;

  /**
   * Persisted map from problem slug to saved code string. This is the only
   * field written to localStorage -- it allows users to resume their work
   * across browser sessions.
   */
  savedCodes: Record<string, string>;

  /**
   * Update the live editor content and mark the editor as dirty.
   * Called on every keystroke or programmatic code change.
   * @param code - The new editor content.
   */
  setCode: (code: string) => void;

  /**
   * Set the active problem slug. Typically called alongside `loadCode()`
   * when navigating to a new problem.
   * @param slug - The problem slug, or null to clear.
   */
  setProblemSlug: (slug: string | null) => void;

  /**
   * Persist the current editor code into `savedCodes` under the active
   * problem slug. Marks the editor as not dirty. No-op if no problem
   * slug is set.
   */
  saveCode: () => void;

  /**
   * Load code for a problem. If previously saved code exists for the slug,
   * it takes priority over the default template. Sets the editor state
   * (code, slug) and marks as not dirty.
   *
   * @param slug - The problem slug to load code for.
   * @param defaultCode - The problem's template code, used as fallback
   *   if no saved code exists for this slug.
   * @returns The code that was loaded (either saved or default).
   */
  loadCode: (slug: string, defaultCode: string) => string;

  /**
   * Reset the editor to the problem's default template. Removes any saved
   * code for the current problem slug from `savedCodes` and marks as not dirty.
   * No-op if no problem slug is set.
   *
   * @param defaultCode - The problem's original template to restore.
   */
  resetCode: (defaultCode: string) => void;
}

/* ─── Store Creation ────────────────────────────────────────────────────── */

export const useEditorStore = create<EditorState>()(
  persist(
    (set, get) => ({
      code: '',
      problemSlug: null,
      isDirty: false,
      savedCodes: {},

      setCode: (code: string) => {
        set({ code, isDirty: true });
      },

      setProblemSlug: (slug: string | null) => {
        set({ problemSlug: slug });
      },

      saveCode: () => {
        const { code, problemSlug, savedCodes } = get();
        if (problemSlug) {
          set({
            savedCodes: { ...savedCodes, [problemSlug]: code },
            isDirty: false,
          });
        }
      },

      loadCode: (slug: string, defaultCode: string) => {
        const { savedCodes } = get();
        const saved = savedCodes[slug];
        /**
         * Prefer saved code over the default template. This allows the user
         * to resume exactly where they left off in a previous session.
         * If no saved code exists, fall back to the problem's template
         * (which typically ends with "Admitted." as a placeholder).
         */
        const code = saved ?? defaultCode;
        set({ code, problemSlug: slug, isDirty: false });
        return code;
      },

      resetCode: (defaultCode: string) => {
        const { problemSlug, savedCodes } = get();
        if (problemSlug) {
          /**
           * Create a shallow copy of savedCodes and delete the entry for
           * the current problem. This ensures the next `loadCode()` call
           * will use the default template rather than the stale saved code.
           */
          const newSavedCodes = { ...savedCodes };
          delete newSavedCodes[problemSlug];
          set({
            code: defaultCode,
            savedCodes: newSavedCodes,
            isDirty: false,
          });
        }
      },
    }),

    /* ── Persistence Configuration ──────────────────────────────────────── */
    {
      /** localStorage key for this store's persisted state. */
      name: 'leetmethods-editor',

      /**
       * Uses safeStorage, a wrapper around localStorage that catches
       * QuotaExceededError to prevent crashes when storage is full.
       */
      storage: safeStorage,

      /**
       * Only persist the `savedCodes` map. The live editor state (code,
       * problemSlug, isDirty) is ephemeral and re-established each time
       * the user navigates to a problem page. Persisting these would cause
       * stale state issues on page load.
       */
      partialize: (state) => ({ savedCodes: state.savedCodes }),
    }
  )
);
