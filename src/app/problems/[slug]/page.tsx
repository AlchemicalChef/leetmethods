import { notFound } from 'next/navigation';
import { ProblemSolver } from '@/components/problem/ProblemSolver';
import { getAllProblems, getProblemSummaries } from '@/lib/problems/loader';

interface Props {
  params: Promise<{ slug: string }>;
}

export async function generateStaticParams() {
  const problems = await getAllProblems();
  return problems.map((problem) => ({
    slug: problem.slug,
  }));
}

export default async function ProblemPage({ params }: Props) {
  const { slug } = await params;
  const problems = await getAllProblems();
  const problem = problems.find((p) => p.slug === slug);

  if (!problem) {
    notFound();
  }

  const allProblems = await getProblemSummaries();

  return <ProblemSolver problem={problem} allProblems={allProblems} />;
}
