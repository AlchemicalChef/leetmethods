'use client';

import { useParams } from 'next/navigation';
import Link from 'next/link';
import { Badge } from '@/components/ui/badge';
import { ArrowLeft } from 'lucide-react';
import { getPathBySlug } from '@/lib/paths/loader';
import { PathStepList } from '@/components/learn/PathStepList';
import { useProgressStore } from '@/store/progressStore';
import { computePathProgress } from '@/lib/paths/progress';
import { PATH_DIFFICULTY_COLORS } from '@/lib/ui-constants';

export default function PathDetailPage() {
  const params = useParams();
  const slug = params.slug as string;
  const path = getPathBySlug(slug);
  const progress = useProgressStore((s) => s.progress);

  if (!path) {
    return (
      <div className="max-w-4xl mx-auto px-4 py-12 text-center">
        <h1 className="text-2xl font-bold mb-4">Path not found</h1>
        <Link href="/learn" className="text-primary hover:underline">
          Back to Learn
        </Link>
      </div>
    );
  }

  const pathProgress = computePathProgress(path, progress);

  return (
    <div className="max-w-4xl mx-auto px-4 py-12">
      <Link
        href="/learn"
        className="inline-flex items-center gap-1 text-sm text-muted-foreground hover:text-foreground mb-6"
      >
        <ArrowLeft className="h-4 w-4" />
        Back to Learn
      </Link>

      <div className="flex items-start gap-4 mb-6">
        <span className="text-4xl">{path.icon}</span>
        <div>
          <div className="flex items-center gap-2 mb-1">
            <h1 className="text-3xl font-bold">{path.title}</h1>
            <Badge className={PATH_DIFFICULTY_COLORS[path.difficulty]}>
              {path.difficulty}
            </Badge>
          </div>
          <p className="text-muted-foreground">{path.description}</p>
        </div>
      </div>

      {/* Progress bar */}
      <div className="flex items-center gap-3 mb-8">
        <div className="flex-1 h-2 bg-muted rounded-full overflow-hidden">
          <div
            className="h-full bg-primary rounded-full transition-all duration-500"
            style={{ width: `${pathProgress.percent}%` }}
          />
        </div>
        <span className="text-sm font-medium">
          {pathProgress.completedSteps}/{pathProgress.totalSteps} complete
        </span>
      </div>

      {/* Steps */}
      <PathStepList steps={path.steps} />
    </div>
  );
}
