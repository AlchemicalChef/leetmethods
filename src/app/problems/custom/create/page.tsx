/**
 * @module CreateCustomProblemPage
 *
 * Client-rendered page for the `/problems/custom/create` route.
 *
 * This page allows users to author their own Coq proof problems using a
 * form-based interface. Custom problems are stored in the Zustand
 * `customProblemStore` (persisted in localStorage), completely separate
 * from the built-in problem registry.
 *
 * Architecture notes:
 * - This must be a **client component** ('use client') because it:
 *   (a) uses `useRouter()` for programmatic navigation after save,
 *   (b) reads from the `customProblemStore` Zustand store.
 * - The `CustomProblemForm` component handles all form state, validation,
 *   and field rendering. This page only wires up the save/cancel callbacks.
 * - When saving, the form data is processed before storage:
 *   - Tags are split from a comma-separated string into an array, trimmed,
 *     and empty strings are filtered out.
 *   - Hints are filtered to remove empty entries.
 *   - `forbiddenTactics` is hardcoded to `['admit', 'Admitted']` to prevent
 *     trivially completed custom problems.
 * - The `addProblem` store action generates a unique slug from the title,
 *   taking care to avoid collisions with existing built-in problem slugs
 *   (passed via `existingSlugs`).
 * - After saving, the user is navigated to the new problem's solve page
 *   at `/problems/custom/{slug}`.
 */
'use client';

import { useRouter } from 'next/navigation';
import { CustomProblemForm } from '@/components/problem/CustomProblemForm';
import { useCustomProblemStore } from '@/store/customProblemStore';
import { getAllProblems } from '@/lib/problems/loader';

/**
 * Page component for creating a new custom problem.
 *
 * Renders the `CustomProblemForm` with save and cancel handlers.
 * On save, the problem is added to the custom problem store and the
 * user is redirected to the newly created problem's page.
 *
 * @returns The custom problem creation form inside a centered layout.
 */
export default function CreateCustomProblemPage() {
  const router = useRouter();
  const addProblem = useCustomProblemStore((s) => s.addProblem);

  return (
    <div className="max-w-3xl mx-auto px-4 py-8">
      <h1 className="text-3xl font-bold mb-6">Create Custom Problem</h1>
      <CustomProblemForm
        onSave={(data) => {
          /**
           * Collect all existing built-in problem slugs so the store can
           * generate a unique slug that does not collide with any built-in
           * problem. This prevents URL conflicts between `/problems/{slug}`
           * (built-in) and `/problems/custom/{slug}` (custom) -- although
           * they are on different route segments, consistent unique slugs
           * help avoid user confusion.
           */
          const existingSlugs = getAllProblems().map((p) => p.slug);
          const slug = addProblem(
            {
              title: data.title,
              difficulty: data.difficulty,
              category: data.category,
              tags: data.tags.split(',').map((t) => t.trim()).filter(Boolean),
              description: data.description,
              hints: data.hints.filter(Boolean),
              prelude: data.prelude,
              template: data.template,
              solution: data.solution,
              forbiddenTactics: ['admit', 'Admitted'],
            },
            existingSlugs
          );
          router.push(`/problems/custom/${slug}`);
        }}
        onCancel={() => router.push('/problems')}
      />
    </div>
  );
}
