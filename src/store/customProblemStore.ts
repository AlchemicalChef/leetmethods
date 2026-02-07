import { create } from 'zustand';
import { persist } from 'zustand/middleware';
import type { Problem, ProblemSummary } from '@/lib/problems/types';
import { generateSlug } from '@/lib/problems/slug';

interface CustomProblemStore {
  problems: Record<string, Problem>;
  addProblem: (problem: Omit<Problem, 'id' | 'slug'>, existingSlugs: string[]) => string;
  updateProblem: (slug: string, updates: Partial<Omit<Problem, 'id' | 'slug'>>) => void;
  deleteProblem: (slug: string) => void;
  getProblem: (slug: string) => Problem | null;
  getAllCustomProblems: () => Problem[];
  getCustomSummaries: () => ProblemSummary[];
  exportProblems: () => string;
  importProblems: (json: string) => { imported: number; errors: string[] };
}

let nextId = Date.now();

export const useCustomProblemStore = create<CustomProblemStore>()(
  persist(
    (set, get) => ({
      problems: {},

      addProblem: (problem, existingSlugs) => {
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
            if (!item.title || !item.template || !item.solution) {
              errors.push(`Skipped problem "${item.title || 'untitled'}": missing required fields`);
              continue;
            }
            const slug = generateSlug(item.title, [...allSlugs, ...Object.keys(newProblems)]);
            const id = `custom-${nextId++}`;
            newProblems[slug] = {
              id,
              slug,
              title: item.title,
              difficulty: item.difficulty || 'medium',
              category: item.category || 'logic',
              tags: item.tags || [],
              description: item.description || '',
              hints: item.hints || [],
              prelude: item.prelude || '',
              template: item.template,
              solution: item.solution,
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
    {
      name: 'leetmethods-custom-problems',
      version: 1,
    }
  )
);
