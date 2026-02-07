'use client';

import { useRouter } from 'next/navigation';
import { CustomProblemForm } from '@/components/problem/CustomProblemForm';
import { useCustomProblemStore } from '@/store/customProblemStore';
import { getAllProblemsSync } from '@/lib/problems/loader';

export default function CreateCustomProblemPage() {
  const router = useRouter();
  const addProblem = useCustomProblemStore((s) => s.addProblem);

  return (
    <div className="max-w-3xl mx-auto px-4 py-8">
      <h1 className="text-3xl font-bold mb-6">Create Custom Problem</h1>
      <CustomProblemForm
        onSave={(data) => {
          const existingSlugs = getAllProblemsSync().map((p) => p.slug);
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
