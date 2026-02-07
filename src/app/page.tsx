import Link from 'next/link';
import { Button } from '@/components/ui/button';
import { Card } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import { ArrowRight, BookOpen, Code, Trophy, Zap } from 'lucide-react';

export default function Home() {
  return (
    <div className="min-h-screen">
      {/* Hero section */}
      <section className="py-20 px-4">
        <div className="max-w-4xl mx-auto text-center">
          <Badge variant="secondary" className="mb-4">
            Learn Formal Verification
          </Badge>
          <h1 className="text-5xl font-bold mb-6">
            Master Coq Proofs
            <span className="text-primary block mt-2">One Theorem at a Time</span>
          </h1>
          <p className="text-xl text-muted-foreground mb-8 max-w-2xl mx-auto">
            LeetMethods is an interactive platform for practicing formal proofs in Coq.
            Solve challenges, build your skills, and prove theorems directly in your browser.
          </p>
          <div className="flex gap-4 justify-center">
            <Link href="/tutorial">
              <Button size="lg" className="gap-2">
                Start Tutorial
                <ArrowRight className="h-4 w-4" />
              </Button>
            </Link>
            <Link href="/problems">
              <Button size="lg" variant="outline">
                Browse Problems
              </Button>
            </Link>
          </div>
        </div>
      </section>

      {/* Features section */}
      <section className="py-16 px-4 bg-muted/30">
        <div className="max-w-6xl mx-auto">
          <h2 className="text-3xl font-bold text-center mb-12">Why LeetMethods?</h2>
          <div className="grid md:grid-cols-2 lg:grid-cols-4 gap-6">
            <FeatureCard
              icon={<Code className="h-8 w-8" />}
              title="Browser-Based"
              description="No installation needed. Write and verify Coq proofs directly in your browser with jsCoq."
            />
            <FeatureCard
              icon={<Zap className="h-8 w-8" />}
              title="Instant Feedback"
              description="See your proof goals update in real-time as you apply tactics."
            />
            <FeatureCard
              icon={<BookOpen className="h-8 w-8" />}
              title="Curated Problems"
              description="Problems organized by difficulty and category, from basic logic to advanced induction."
            />
            <FeatureCard
              icon={<Trophy className="h-8 w-8" />}
              title="Track Progress"
              description="Your solutions are saved locally. Watch your completion rate grow."
            />
          </div>
        </div>
      </section>

      {/* Categories section */}
      <section className="py-16 px-4">
        <div className="max-w-4xl mx-auto">
          <h2 className="text-3xl font-bold text-center mb-12">Problem Categories</h2>
          <div className="grid sm:grid-cols-2 lg:grid-cols-3 gap-4">
            <CategoryCard
              title="Logic"
              description="Propositional and predicate logic proofs"
              count={6}
            />
            <CategoryCard
              title="Induction"
              description="Mathematical and structural induction"
              count={5}
            />
            <CategoryCard
              title="Lists"
              description="Proofs about list operations"
              count={5}
            />
            <CategoryCard
              title="Arithmetic"
              description="Number theory and arithmetic proofs"
              count={5}
            />
            <CategoryCard
              title="Data Structures"
              slug="data-structures"
              description="Trees, BSTs, and recursive data types"
              count={4}
            />
            <CategoryCard
              title="Relations"
              description="Ordering, equality, and relational proofs"
              count={5}
            />
          </div>
        </div>
      </section>

      {/* CTA section */}
      <section className="py-20 px-4 bg-primary/5">
        <div className="max-w-2xl mx-auto text-center">
          <h2 className="text-3xl font-bold mb-4">Ready to Start?</h2>
          <p className="text-muted-foreground mb-8">
            Jump into your first proof. No signup required.
          </p>
          <Link href="/problems/modus-ponens">
            <Button size="lg" className="gap-2">
              Try Your First Problem
              <ArrowRight className="h-4 w-4" />
            </Button>
          </Link>
        </div>
      </section>

      {/* Footer */}
      <footer className="py-8 px-4 border-t">
        <div className="max-w-4xl mx-auto text-center text-sm text-muted-foreground">
          <p>Built with Next.js, CodeMirror, and jsCoq</p>
          <p className="mt-2">
            Inspired by{' '}
            <a
              href="https://softwarefoundations.cis.upenn.edu/"
              target="_blank"
              rel="noopener noreferrer"
              className="underline hover:text-foreground"
            >
              Software Foundations
            </a>
          </p>
        </div>
      </footer>
    </div>
  );
}

function FeatureCard({
  icon,
  title,
  description,
}: {
  icon: React.ReactNode;
  title: string;
  description: string;
}) {
  return (
    <Card className="p-6 text-center">
      <div className="inline-flex items-center justify-center w-16 h-16 rounded-full bg-primary/10 text-primary mb-4">
        {icon}
      </div>
      <h3 className="font-semibold mb-2">{title}</h3>
      <p className="text-sm text-muted-foreground">{description}</p>
    </Card>
  );
}

function CategoryCard({
  title,
  description,
  count,
  slug,
}: {
  title: string;
  description: string;
  count: number;
  slug?: string;
}) {
  return (
    <Link href={`/problems?category=${slug ?? title.toLowerCase()}`}>
      <Card className="p-4 hover:bg-muted/50 transition-colors cursor-pointer">
        <div className="flex justify-between items-start">
          <div>
            <h3 className="font-semibold">{title}</h3>
            <p className="text-sm text-muted-foreground mt-1">{description}</p>
          </div>
          <Badge variant="secondary">{count}</Badge>
        </div>
      </Card>
    </Link>
  );
}
