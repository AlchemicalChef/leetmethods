import { notFound } from 'next/navigation';
import { ProblemSolver } from '@/components/problem/ProblemSolver';
import { getAllProblems, getProblemSummaries } from '@/lib/problems/loader';
import type { Metadata } from 'next';

interface Props {
  params: Promise<{ slug: string }>;
}

export async function generateStaticParams() {
  const problems = await getAllProblems();
  return problems.map((problem) => ({
    slug: problem.slug,
  }));
}

export async function generateMetadata({ params }: Props): Promise<Metadata> {
  const { slug } = await params;
  const problems = await getAllProblems();
  const problem = problems.find((p) => p.slug === slug);

  if (!problem) {
    return { title: 'Problem Not Found - LeetMethods' };
  }

  return {
    title: `${problem.title} - LeetMethods`,
    description: `Solve "${problem.title}" - a ${problem.difficulty} ${problem.category} proof problem. Practice formal verification in Coq.`,
  };
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
