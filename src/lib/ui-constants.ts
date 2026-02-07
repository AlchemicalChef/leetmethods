import type { Difficulty, Category } from '@/lib/problems/types';

export const DIFFICULTY_COLORS: Record<Difficulty, string> = {
  easy: 'bg-green-100 text-green-800 dark:bg-green-900 dark:text-green-200',
  medium: 'bg-yellow-100 text-yellow-800 dark:bg-yellow-900 dark:text-yellow-200',
  hard: 'bg-red-100 text-red-800 dark:bg-red-900 dark:text-red-200',
};

export const PATH_DIFFICULTY_COLORS: Record<string, string> = {
  beginner: 'bg-green-100 text-green-800 dark:bg-green-900 dark:text-green-200',
  intermediate: 'bg-yellow-100 text-yellow-800 dark:bg-yellow-900 dark:text-yellow-200',
  advanced: 'bg-red-100 text-red-800 dark:bg-red-900 dark:text-red-200',
};

export const DIFFICULTY_ORDER: Record<Difficulty, number> = { easy: 0, medium: 1, hard: 2 };

export const CATEGORY_LABELS: Record<Category, string> = {
  logic: 'Logic',
  induction: 'Induction',
  lists: 'Lists',
  arithmetic: 'Arithmetic',
  'data-structures': 'Data Structures',
  relations: 'Relations',
};

export const CATEGORY_COLORS: Record<Category, string> = {
  logic: 'bg-blue-500',
  induction: 'bg-purple-500',
  lists: 'bg-emerald-500',
  arithmetic: 'bg-orange-500',
  'data-structures': 'bg-pink-500',
  relations: 'bg-cyan-500',
};

export const CATEGORY_ORDER: Category[] = [
  'logic',
  'induction',
  'lists',
  'arithmetic',
  'data-structures',
  'relations',
];
