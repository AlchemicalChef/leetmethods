export interface PathStep {
  problemSlug: string;
  title: string;
  description: string;
}

export interface LearningPath {
  slug: string;
  title: string;
  description: string;
  difficulty: 'beginner' | 'intermediate' | 'advanced';
  icon: string;
  steps: PathStep[];
}
