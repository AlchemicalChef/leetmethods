/**
 * @module EditCustomProblemPage
 *
 * Client-rendered page for the `/problems/custom/[slug]/edit` route.
 *
 * This page allows users to modify an existing custom problem they previously
 * created. It reuses the same `CustomProblemForm` component used for creation
 * but pre-populates it with the problem's current data and passes the
 * `isEditing` flag to adjust the form's UI (e.g., button labels).
 *
 * Architecture notes:
 * - Like the custom problem solve page, this component uses a **hydration
 *   guard** (`hydrated` state) to wait for the Zustand `customProblemStore`
 *   to rehydrate from localStorage before attempting to read the problem.
 *   Without this, the component would render a "not found" state during
 *   the brief window between SSR and localStorage rehydration.
 * - The `updateProblem` store action performs an in-place update of the
 *   problem in localStorage, preserving the original slug. This means
 *   changing the title does NOT change the URL slug -- the slug is stable
 *   once created.
 * - After saving, the user is redirected to the custom problem's solve
 *   page. Canceling also returns to the solve page (not the problems list),
 *   since the user was viewing the problem before clicking "Edit".
 * - Tags are stored as an array but edited as a comma-separated string,
 *   so the form receives `tags.join(', ')` and the save handler splits
 *   them back into an array.
 * - If the problem has no hints, the form receives `['']` (an array with
 *   one empty string) so the hints input field is visible but empty,
 *   rather than showing no hint fields at all.
 */
'use client';

import { useEffect, useState } from 'react';
import { useParams, useRouter } from 'next/navigation';
import { useCustomProblemStore } from '@/store/customProblemStore';
import { CustomProblemForm } from '@/components/problem/CustomProblemForm';

/**
 * Page component for editing an existing custom problem.
 *
 * Loads the problem from the custom problem store after hydration,
 * renders the `CustomProblemForm` with pre-populated data, and handles
 * save/cancel navigation.
 *
 * @returns A loading spinner during hydration, a "not found" message if
 *   the problem does not exist, or the edit form pre-filled with the
 *   problem's current data.
 */
export default function EditCustomProblemPage() {
  const params = useParams();
  const router = useRouter();
  const slug = params.slug as string;
  const getProblem = useCustomProblemStore((s) => s.getProblem);
  const updateProblem = useCustomProblemStore((s) => s.updateProblem);

  /**
   * Hydration flag: ensures localStorage-backed Zustand store is ready
   * before we try to read the problem data. See CustomProblemPage for
   * a detailed explanation of why this is necessary.
   */
  const [hydrated, setHydrated] = useState(false);

  useEffect(() => {
    setHydrated(true);
  }, []);

  /* ---------------------------------------------------------------- */
  /*  Pre-hydration loading spinner                                    */
  /* ---------------------------------------------------------------- */

  if (!hydrated) {
    return (
      <div className="flex items-center justify-center h-[calc(100vh-64px)]">
        <div className="animate-spin rounded-full h-8 w-8 border-2 border-primary border-t-transparent" />
      </div>
    );
  }

  /* ---------------------------------------------------------------- */
  /*  Problem lookup (post-hydration)                                  */
  /* ---------------------------------------------------------------- */

  const problem = getProblem(slug);

  if (!problem) {
    return (
      <div className="max-w-4xl mx-auto px-4 py-16 text-center">
        <h1 className="text-2xl font-bold mb-4">Custom Problem Not Found</h1>
        <button onClick={() => router.push('/problems')} className="text-primary hover:underline">
          Back to Problems
        </button>
      </div>
    );
  }

  /* ---------------------------------------------------------------- */
  /*  Render edit form                                                 */
  /* ---------------------------------------------------------------- */

  return (
    <div className="max-w-3xl mx-auto px-4 py-8">
      <h1 className="text-3xl font-bold mb-6">Edit: {problem.title}</h1>
      <CustomProblemForm
        initialData={{
          title: problem.title,
          difficulty: problem.difficulty,
          category: problem.category,
          tags: problem.tags.join(', '),
          description: problem.description,
          prelude: problem.prelude,
          template: problem.template,
          solution: problem.solution,
          /**
           * Ensure at least one hint field is visible in the form. If the
           * problem has no hints, provide a single empty string so the
           * dynamic hints input renders one empty row.
           */
          hints: problem.hints.length > 0 ? problem.hints : [''],
        }}
        isEditing
        onSave={(data) => {
          /**
           * Update the problem in-place. The slug remains unchanged even
           * if the title is modified -- slug stability is important for
           * bookmarked URLs and editor state stored by slug in editorStore.
           */
          updateProblem(slug, {
            title: data.title,
            difficulty: data.difficulty,
            category: data.category,
            tags: data.tags.split(',').map((t) => t.trim()).filter(Boolean),
            description: data.description,
            hints: data.hints.filter(Boolean),
            prelude: data.prelude,
            template: data.template,
            solution: data.solution,
          });
          router.push(`/problems/custom/${slug}`);
        }}
        onCancel={() => router.push(`/problems/custom/${slug}`)}
      />
    </div>
  );
}
