import { NextResponse } from 'next/server';
import { getProblemSummaries } from '@/lib/problems/loader';

export async function GET() {
  const problems = await getProblemSummaries();
  return NextResponse.json(problems);
}
