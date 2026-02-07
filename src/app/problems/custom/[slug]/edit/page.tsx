'use client';

import { useEffect, useState } from 'react';
import { useParams, useRouter } from 'next/navigation';
import { useCustomProblemStore } from '@/store/customProblemStore';
import { CustomProblemForm } from '@/components/problem/CustomProblemForm';

export default function EditCustomProblemPage() {
  const params = useParams();
  const router = useRouter();
  const slug = params.slug as string;
  const getProblem = useCustomProblemStore((s) => s.getProblem);
  const updateProblem = useCustomProblemStore((s) => s.updateProblem);
  const [hydrated, setHydrated] = useState(false);

  useEffect(() => {
    setHydrated(true);
  }, []);

  if (!hydrated) {
    return (
      <div className="flex items-center justify-center h-[calc(100vh-64px)]">
        <div className="animate-spin rounded-full h-8 w-8 border-2 border-primary border-t-transparent" />
      </div>
    );
  }

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
          hints: problem.hints.length > 0 ? problem.hints : [''],
        }}
        isEditing
        onSave={(data) => {
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
