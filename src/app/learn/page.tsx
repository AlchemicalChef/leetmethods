import Link from 'next/link';
import { Card } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import { ArrowRight, BookOpen, Lightbulb, Zap } from 'lucide-react';

export default function LearnPage() {
  return (
    <div className="max-w-4xl mx-auto px-4 py-12">
      <h1 className="text-4xl font-bold mb-4">Learn Coq</h1>
      <p className="text-xl text-muted-foreground mb-8">
        A gentle introduction to theorem proving with Coq
      </p>

      <div className="space-y-6">
        <Section
          title="Getting Started"
          description="New to Coq? Start here."
        >
          <TopicCard
            icon={<BookOpen className="h-5 w-5" />}
            title="What is Coq?"
            description="Learn what Coq is and why formal verification matters"
            href="/learn/intro"
            badge="Beginner"
          />
          <TopicCard
            icon={<Lightbulb className="h-5 w-5" />}
            title="Basic Tactics"
            description="Learn the essential tactics: intros, apply, exact, reflexivity"
            href="/problems/modus-ponens"
            badge="Beginner"
          />
        </Section>

        <Section
          title="Core Concepts"
          description="Master the fundamentals"
        >
          <TopicCard
            icon={<Zap className="h-5 w-5" />}
            title="Induction"
            description="Learn proof by induction on natural numbers and lists"
            href="/problems/plus-n-zero"
            badge="Essential"
          />
          <TopicCard
            icon={<Zap className="h-5 w-5" />}
            title="Working with Lists"
            description="Prove properties about list operations"
            href="/problems/list-length-app"
            badge="Intermediate"
          />
        </Section>

        <Section
          title="Reference"
          description="Quick references and cheat sheets"
        >
          <Card className="p-6">
            <h3 className="font-semibold mb-4">Common Tactics</h3>
            <div className="grid grid-cols-2 gap-4 text-sm">
              <TacticRef name="intros" desc="Introduce hypotheses" />
              <TacticRef name="apply H" desc="Use hypothesis H" />
              <TacticRef name="exact H" desc="Prove goal with H" />
              <TacticRef name="reflexivity" desc="Prove x = x" />
              <TacticRef name="simpl" desc="Simplify expressions" />
              <TacticRef name="rewrite H" desc="Replace using equality H" />
              <TacticRef name="induction n" desc="Induction on n" />
              <TacticRef name="destruct H" desc="Case analysis on H" />
              <TacticRef name="split" desc="Prove P /\\ Q" />
              <TacticRef name="left/right" desc="Prove P \\/ Q" />
            </div>
          </Card>
        </Section>

        <div className="bg-muted/30 rounded-lg p-6 mt-8">
          <h3 className="font-semibold mb-2">Ready to Practice?</h3>
          <p className="text-muted-foreground mb-4">
            The best way to learn Coq is by doing. Jump into the problems!
          </p>
          <Link
            href="/problems"
            className="inline-flex items-center gap-2 text-primary hover:underline"
          >
            Browse Problems
            <ArrowRight className="h-4 w-4" />
          </Link>
        </div>
      </div>
    </div>
  );
}

function Section({
  title,
  description,
  children,
}: {
  title: string;
  description: string;
  children: React.ReactNode;
}) {
  return (
    <div>
      <h2 className="text-2xl font-semibold mb-2">{title}</h2>
      <p className="text-muted-foreground mb-4">{description}</p>
      <div className="grid md:grid-cols-2 gap-4">{children}</div>
    </div>
  );
}

function TopicCard({
  icon,
  title,
  description,
  href,
  badge,
}: {
  icon: React.ReactNode;
  title: string;
  description: string;
  href: string;
  badge: string;
}) {
  return (
    <Link href={href}>
      <Card className="p-4 h-full hover:bg-muted/50 transition-colors">
        <div className="flex items-start gap-3">
          <div className="p-2 rounded-md bg-primary/10 text-primary">
            {icon}
          </div>
          <div className="flex-1">
            <div className="flex items-center gap-2 mb-1">
              <h3 className="font-medium">{title}</h3>
              <Badge variant="secondary" className="text-xs">
                {badge}
              </Badge>
            </div>
            <p className="text-sm text-muted-foreground">{description}</p>
          </div>
        </div>
      </Card>
    </Link>
  );
}

function TacticRef({ name, desc }: { name: string; desc: string }) {
  return (
    <div>
      <code className="text-primary font-mono text-xs">{name}</code>
      <span className="text-muted-foreground ml-2">{desc}</span>
    </div>
  );
}
