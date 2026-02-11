/**
 * @module customProblemStore
 *
 * Persisted Zustand store for user-created custom problems.
 *
 * LeetMethods ships with a curated set of built-in problems (loaded from
 * JSON files via `src/lib/problems/loader.ts`), but users can also create
 * their own Coq proof problems. This store manages the full lifecycle of
 * custom problems: creation, editing, deletion, and JSON import/export.
 *
 * Custom problems are stored as full `Problem` objects keyed by their
 * generated slug. Each custom problem gets a unique ID in the format
 * "custom-{timestamp}" and a slug derived from the title (with collision
 * avoidance against both built-in and existing custom problem slugs).
 *
 * Persistence:
 * - Persisted to localStorage via `safeStorage` under key "leetmethods-custom-problems".
 * - Schema version 1 (no migrations needed yet).
 * - On rehydration from localStorage, `ensureNextIdFromState()` scans existing
 *   problem IDs to advance the `nextId` counter past any previously used IDs.
 *   This prevents ID collisions after page reload.
 *
 * Import/Export:
 * - `exportProblems()` serializes all custom problems to a JSON string.
 * - `importProblems()` parses a JSON array, validates required fields,
 *   generates fresh slugs/IDs, and applies sensible defaults for optional
 *   fields. It returns a report of how many were imported and any errors.
 *
 * Integration:
 * - The problems page merges custom problems with built-in ones via
 *   `getCustomSummaries()`, which returns `ProblemSummary` objects with
 *   `isCustom: true` so the UI can distinguish them.
 * - Custom problems use the same `Problem` type as built-in ones, so they
 *   work with ProblemSolver, the editor, and the progress system unchanged.
 */

import { create } from 'zustand';
import { persist } from 'zustand/middleware';
import type { Problem, ProblemSummary, Difficulty } from '@/lib/problems/types';
import { generateSlug } from '@/lib/problems/slug';
import { safeStorage } from '@/lib/safe-storage';
import { CATEGORY_ORDER } from '@/lib/ui-constants';

/**
 * Whitelist of valid difficulty values. Used during import to sanitize
 * user-provided difficulty strings -- invalid values fall back to 'medium'.
 */
const VALID_DIFFICULTIES: Difficulty[] = ['easy', 'medium', 'hard'];

/* ─── Store Interface ───────────────────────────────────────────────────── */

interface CustomProblemStore {
  /** Map from problem slug to the full Problem object. */
  problems: Record<string, Problem>;

  /**
   * Create a new custom problem with auto-generated ID and slug.
   *
   * @param problem - The problem data (without id/slug, which are generated).
   * @param existingSlugs - Array of built-in problem slugs to avoid collisions with.
   * @returns The generated slug for the new problem.
   */
  addProblem: (problem: Omit<Problem, 'id' | 'slug'>, existingSlugs: string[]) => string;

  /**
   * Update fields of an existing custom problem. The slug and id cannot
   * be changed (they are excluded from the updates type).
   *
   * @param slug - The slug of the problem to update.
   * @param updates - Partial problem fields to merge into the existing record.
   */
  updateProblem: (slug: string, updates: Partial<Omit<Problem, 'id' | 'slug'>>) => void;

  /**
   * Delete a custom problem by its slug.
   *
   * @param slug - The slug of the problem to remove.
   */
  deleteProblem: (slug: string) => void;

  /**
   * Retrieve a single custom problem by slug.
   *
   * @param slug - The slug to look up.
   * @returns The Problem object, or null if not found.
   */
  getProblem: (slug: string) => Problem | null;

  /**
   * Get all custom problems as an array.
   *
   * @returns Array of all custom Problem objects.
   */
  getAllCustomProblems: () => Problem[];

  /**
   * Get lightweight summaries of all custom problems for list display.
   * Each summary includes the `isCustom: true` flag so the UI can
   * distinguish custom problems from built-in ones.
   *
   * @returns Array of ProblemSummary objects with isCustom set to true.
   */
  getCustomSummaries: () => ProblemSummary[];

  /**
   * Serialize all custom problems to a formatted JSON string for export.
   *
   * @returns JSON string representation of the custom problems array.
   */
  exportProblems: () => string;

  /**
   * Import problems from a JSON string. Validates required fields (title,
   * template, solution), generates fresh slugs/IDs, and applies defaults
   * for optional fields. Skips invalid entries and reports errors.
   *
   * @param json - A JSON string containing an array of problem objects.
   * @returns An object with `imported` (count of successfully imported problems)
   *   and `errors` (array of human-readable error messages for skipped items).
   */
  importProblems: (json: string) => { imported: number; errors: string[] };
}

/* ─── ID Generation ─────────────────────────────────────────────────────── */

/**
 * Module-level counter for generating unique custom problem IDs.
 * Initialized to the current timestamp and incremented with each new problem.
 * This provides monotonically increasing, collision-resistant IDs.
 *
 * IMPORTANT: After rehydration from localStorage, `ensureNextIdFromState()`
 * advances this counter past any existing IDs to prevent collisions. Without
 * this, a page reload could reuse a timestamp that was already assigned.
 */
let nextId = Date.now();

/**
 * Scans all existing custom problems and advances the `nextId` counter
 * past the highest existing ID number. Called during store rehydration
 * (via `onRehydrateStorage`) to prevent ID collisions after page reload.
 *
 * Custom problem IDs follow the format "custom-{number}". This function
 * extracts the numeric portion and ensures `nextId` is always greater.
 *
 * @param problems - The problems record from the rehydrated store state.
 */
function ensureNextIdFromState(problems: Record<string, Problem>): void {
  for (const p of Object.values(problems)) {
    const match = p.id.match(/^custom-(\d+)$/);
    if (match) {
      const n = Number(match[1]);
      if (n >= nextId) nextId = n + 1;
    }
  }
}

/* ─── Store Creation ────────────────────────────────────────────────────── */

export const useCustomProblemStore = create<CustomProblemStore>()(
  persist(
    (set, get) => ({
      problems: {},

      addProblem: (problem, existingSlugs) => {
        /**
         * Merge built-in slugs with existing custom slugs to ensure the
         * generated slug is unique across the entire problem catalog.
         */
        const allSlugs = [...existingSlugs, ...Object.keys(get().problems)];
        const slug = generateSlug(problem.title, allSlugs);
        const id = `custom-${nextId++}`;
        const fullProblem: Problem = { ...problem, id, slug };
        set((state) => ({
          problems: { ...state.problems, [slug]: fullProblem },
        }));
        return slug;
      },

      updateProblem: (slug, updates) => {
        set((state) => {
          const existing = state.problems[slug];
          if (!existing) return state;
          return {
            problems: {
              ...state.problems,
              [slug]: { ...existing, ...updates },
            },
          };
        });
      },

      deleteProblem: (slug) => {
        set((state) => {
          /**
           * Destructure to separate the target problem from the rest.
           * The `_removed` variable is intentionally unused -- we only
           * need the `rest` to form the new problems record without it.
           */
          // eslint-disable-next-line @typescript-eslint/no-unused-vars
          const { [slug]: _removed, ...rest } = state.problems;
          return { problems: rest };
        });
      },

      getProblem: (slug) => {
        return get().problems[slug] ?? null;
      },

      getAllCustomProblems: () => {
        return Object.values(get().problems);
      },

      getCustomSummaries: (): ProblemSummary[] => {
        /**
         * Project each full Problem down to a ProblemSummary, adding
         * `isCustom: true` so the problems list page can render custom
         * problems with a distinguishing badge or filter option.
         */
        return Object.values(get().problems).map(({ id, slug, title, difficulty, category, tags }) => ({
          id,
          slug,
          title,
          difficulty,
          category,
          tags,
          isCustom: true,
        }));
      },

      exportProblems: () => {
        return JSON.stringify(Object.values(get().problems), null, 2);
      },

      importProblems: (json) => {
        const errors: string[] = [];
        let imported = 0;
        try {
          const parsed = JSON.parse(json);
          if (!Array.isArray(parsed)) {
            return { imported: 0, errors: ['Invalid format: expected an array'] };
          }

          const allSlugs = Object.keys(get().problems);
          const newProblems: Record<string, Problem> = {};

          for (const item of parsed) {
            /**
             * Validate required fields. A problem must have at minimum a title,
             * template (the proof skeleton the user fills in), and solution
             * (the reference proof for verification). Everything else has
             * sensible defaults applied below.
             */
            if (!item.title || !item.template || !item.solution) {
              errors.push(`Skipped problem "${item.title || 'untitled'}": missing required fields`);
              continue;
            }

            /**
             * Generate a unique slug considering both existing custom problems
             * and problems being imported in this same batch (via newProblems
             * keys). This prevents collisions within a single import operation.
             */
            const slug = generateSlug(item.title, [...allSlugs, ...Object.keys(newProblems)]);
            const id = `custom-${nextId++}`;

            newProblems[slug] = {
              id,
              slug,
              title: item.title,
              /**
               * Validate difficulty and category against known values.
               * Invalid or missing values fall back to 'medium' and 'logic'
               * respectively, which are safe defaults.
               */
              difficulty: VALID_DIFFICULTIES.includes(item.difficulty) ? item.difficulty : 'medium',
              category: CATEGORY_ORDER.includes(item.category) ? item.category : 'logic',
              tags: Array.isArray(item.tags) ? item.tags : [],
              description: item.description || '',
              hints: item.hints || [],
              prelude: item.prelude || '',
              template: item.template,
              solution: item.solution,
              /**
               * Default forbidden tactics include 'admit' and 'Admitted', which
               * are the standard Coq "give up" tactics. Problem templates end
               * with 'Admitted.' by convention, so the verifier catches
               * unmodified submissions.
               */
              forbiddenTactics: item.forbiddenTactics || ['admit', 'Admitted'],
            };
            imported++;
          }

          set((state) => ({
            problems: { ...state.problems, ...newProblems },
          }));
        } catch {
          errors.push('Failed to parse JSON');
        }
        return { imported, errors };
      },
    }),

    /* ── Persistence Configuration ──────────────────────────────────────── */
    {
      /** localStorage key for this store's persisted state. */
      name: 'leetmethods-custom-problems',

      /** Schema version. Currently v1 with no migrations. */
      version: 1,

      /**
       * Uses safeStorage, a wrapper around localStorage that catches
       * QuotaExceededError to prevent crashes when storage is full.
       */
      storage: safeStorage,

      /**
       * Rehydration callback. After the store loads persisted state from
       * localStorage, we need to advance the `nextId` counter past any
       * existing custom problem IDs. Without this, `nextId` would be
       * re-initialized to `Date.now()` on each page load, which could be
       * lower than a previously assigned ID if the clock hasn't advanced
       * enough, leading to ID collisions.
       */
      onRehydrateStorage: () => (state) => {
        if (state?.problems) {
          ensureNextIdFromState(state.problems);
        }
      },
    }
  )
);
