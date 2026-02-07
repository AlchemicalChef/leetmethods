import type { Metadata } from 'next';

export const metadata: Metadata = {
  title: 'Tutorial | LeetMethods',
  description: 'Learn the basics of theorem proving in Coq with step-by-step interactive exercises.',
};

export default function TutorialLayout({ children }: { children: React.ReactNode }) {
  return children;
}
