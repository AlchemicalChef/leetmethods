'use client';

import { useState, useMemo } from 'react';
import { Card } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import { Search, ChevronDown, ChevronRight } from 'lucide-react';
import { tacticDocs, type TacticDoc } from '@/lib/coq/tactic-docs';

const categories = Array.from(new Set(tacticDocs.map((t) => t.category)));

export function TacticReference() {
  const [search, setSearch] = useState('');
  const [selectedCategory, setSelectedCategory] = useState<string | null>(null);
  const [expandedTactic, setExpandedTactic] = useState<string | null>(null);

  const filtered = useMemo(() => {
    return tacticDocs.filter((t) => {
      const matchesSearch =
        !search ||
        t.name.toLowerCase().includes(search.toLowerCase()) ||
        t.description.toLowerCase().includes(search.toLowerCase());
      const matchesCategory = !selectedCategory || t.category === selectedCategory;
      return matchesSearch && matchesCategory;
    });
  }, [search, selectedCategory]);

  return (
    <div className="space-y-4">
      {/* Search and filter */}
      <div className="flex flex-col sm:flex-row gap-3">
        <div className="relative flex-1">
          <Search className="absolute left-3 top-1/2 -translate-y-1/2 h-4 w-4 text-muted-foreground" />
          <input
            type="text"
            placeholder="Search tactics..."
            value={search}
            onChange={(e) => setSearch(e.target.value)}
            className="w-full pl-9 pr-3 py-2 border rounded-md bg-background text-sm focus:outline-none focus:ring-2 focus:ring-primary/50"
          />
        </div>
        <div className="flex flex-wrap gap-1">
          <button
            onClick={() => setSelectedCategory(null)}
            className={`px-2 py-1 text-xs rounded-md border transition-colors ${
              !selectedCategory ? 'bg-primary text-primary-foreground' : 'hover:bg-muted'
            }`}
          >
            All
          </button>
          {categories.map((cat) => (
            <button
              key={cat}
              onClick={() => setSelectedCategory(cat === selectedCategory ? null : cat)}
              className={`px-2 py-1 text-xs rounded-md border transition-colors ${
                selectedCategory === cat ? 'bg-primary text-primary-foreground' : 'hover:bg-muted'
              }`}
            >
              {cat}
            </button>
          ))}
        </div>
      </div>

      {/* Results count */}
      <div className="text-sm text-muted-foreground">
        {filtered.length} tactic{filtered.length !== 1 ? 's' : ''}
      </div>

      {/* Tactic list */}
      <div className="space-y-2">
        {filtered.map((tactic) => (
          <TacticCard
            key={tactic.name}
            tactic={tactic}
            expanded={expandedTactic === tactic.name}
            onToggle={() =>
              setExpandedTactic(expandedTactic === tactic.name ? null : tactic.name)
            }
          />
        ))}
      </div>
    </div>
  );
}

function TacticCard({
  tactic,
  expanded,
  onToggle,
}: {
  tactic: TacticDoc;
  expanded: boolean;
  onToggle: () => void;
}) {
  return (
    <Card className="overflow-hidden">
      <button onClick={onToggle} className="w-full p-3 flex items-start gap-3 hover:bg-muted/30 transition-colors text-left">
        {expanded ? (
          <ChevronDown className="h-4 w-4 mt-0.5 shrink-0" />
        ) : (
          <ChevronRight className="h-4 w-4 mt-0.5 shrink-0" />
        )}
        <div className="flex-1 min-w-0">
          <div className="flex items-center gap-2 flex-wrap">
            <code className="font-mono font-semibold text-primary">{tactic.name}</code>
            <Badge variant="secondary" className="text-xs">
              {tactic.category}
            </Badge>
          </div>
          <div className="text-sm text-muted-foreground mt-1 line-clamp-1">{tactic.description}</div>
        </div>
      </button>
      {expanded && (
        <div className="border-t px-3 py-3 space-y-3 bg-muted/10">
          <div>
            <div className="text-xs font-medium text-muted-foreground uppercase mb-1">Signature</div>
            <code className="text-sm font-mono">{tactic.signature}</code>
          </div>
          <div>
            <div className="text-xs font-medium text-muted-foreground uppercase mb-1">Description</div>
            <p className="text-sm">{tactic.description}</p>
          </div>
          <div>
            <div className="text-xs font-medium text-muted-foreground uppercase mb-1">Example</div>
            <pre className="text-sm font-mono bg-muted p-3 rounded-md overflow-x-auto">
              <code>{tactic.example}</code>
            </pre>
          </div>
          {tactic.seeAlso.length > 0 && (
            <div>
              <div className="text-xs font-medium text-muted-foreground uppercase mb-1">See Also</div>
              <div className="flex gap-1 flex-wrap">
                {tactic.seeAlso.map((name) => (
                  <Badge key={name} variant="outline" className="text-xs font-mono">
                    {name}
                  </Badge>
                ))}
              </div>
            </div>
          )}
        </div>
      )}
    </Card>
  );
}
