'use client';

import { getAllPaths } from '@/lib/paths/loader';
import { PathCard } from './PathCard';

export function LearningPathsSection() {
  const paths = getAllPaths();

  return (
    <div>
      <h2 className="text-2xl font-semibold mb-2">Learning Paths</h2>
      <p className="text-muted-foreground mb-4">Follow guided sequences to build your skills</p>
      <div className="grid md:grid-cols-2 lg:grid-cols-3 gap-4">
        {paths.map((path) => (
          <PathCard key={path.slug} path={path} />
        ))}
      </div>
    </div>
  );
}
