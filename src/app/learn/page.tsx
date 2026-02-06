import { LearnHub } from '@/components/learn/LearnHub';

export default function LearnPage() {
  return (
    <div className="max-w-4xl mx-auto px-4 py-12">
      <h1 className="text-4xl font-bold mb-4">Learn Coq</h1>
      <p className="text-xl text-muted-foreground mb-8">
        A gentle introduction to theorem proving with Coq
      </p>
      <LearnHub />
    </div>
  );
}
