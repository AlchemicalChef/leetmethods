import { create } from 'zustand';
import { persist } from 'zustand/middleware';
import { safeStorage } from '@/lib/safe-storage';

interface EditorState {
  code: string;
  problemSlug: string | null;
  isDirty: boolean;
  savedCodes: Record<string, string>; // problemSlug -> code

  setCode: (code: string) => void;
  setProblemSlug: (slug: string | null) => void;
  saveCode: () => void;
  loadCode: (slug: string, defaultCode: string) => string;
  resetCode: (defaultCode: string) => void;
}

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
        const code = saved ?? defaultCode;
        set({ code, problemSlug: slug, isDirty: false });
        return code;
      },

      resetCode: (defaultCode: string) => {
        const { problemSlug, savedCodes } = get();
        if (problemSlug) {
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
    {
      name: 'leetmethods-editor',
      storage: safeStorage,
      partialize: (state) => ({ savedCodes: state.savedCodes }),
    }
  )
);
