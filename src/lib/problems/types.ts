export type Difficulty = 'easy' | 'medium' | 'hard';
export type Category = 'logic' | 'induction' | 'lists' | 'data-structures' | 'relations' | 'arithmetic' | 'booleans';

export interface Problem {
  id: string;
  slug: string;
  title: string;
  difficulty: Difficulty;
  category: Category;
  tags: string[];
  description: string;
  hints: string[];
  prelude: string;
  template: string;
  solution: string;
  forbiddenTactics: string[];
  prerequisites?: {
    problems?: string[];
    concepts?: string[];
  };
}

export interface ProblemSummary {
  id: string;
  slug: string;
  title: string;
  difficulty: Difficulty;
  category: Category;
  tags: string[];
  isCustom?: boolean;
}
