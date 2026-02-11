/**
 * @module TacticReference
 *
 * A searchable, filterable encyclopedia of Coq tactics used in the Learn page.
 *
 * This component provides a comprehensive reference for all Coq tactics
 * documented in the app. Users can:
 *   - Search tactics by name or description via a text input
 *   - Filter by category using toggle buttons
 *   - Expand individual tactic cards to see signature, full description,
 *     usage example, and related tactics
 *
 * The tactic data comes from `tacticDocs` in `src/lib/coq/tactic-docs.ts`,
 * which is a static array of TacticDoc objects.
 *
 * Design decisions:
 *   - Categories are derived from the tactic data at module level (outside
 *     the component) to avoid recomputation on every render.
 *   - The filter is case-insensitive and searches both name and description
 *     fields, providing a forgiving search experience.
 *   - Only one tactic can be expanded at a time (accordion behavior) to
 *     keep the page scannable and avoid overwhelming the user with content.
 *   - The filtered list is memoized with `useMemo` to avoid unnecessary
 *     re-filtering when unrelated state changes (e.g., expanding a card).
 */
'use client';

import { useState, useMemo } from 'react';
import { Card } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import { Search, ChevronDown, ChevronRight } from 'lucide-react';
import { tacticDocs, type TacticDoc } from '@/lib/coq/tactic-docs';

/**
 * Unique tactic categories extracted from the tactic documentation data.
 * Computed once at module load time to avoid repeated Set construction.
 */
const categories = Array.from(new Set(tacticDocs.map((t) => t.category)));

/**
 * Renders the tactic reference section with search, category filters,
 * and expandable tactic cards.
 *
 * @returns The complete tactic reference UI.
 */
export function TacticReference() {
  /** Current search query text (filters by tactic name and description) */
  const [search, setSearch] = useState('');
  /** Currently selected category filter, or null for "All" */
  const [selectedCategory, setSelectedCategory] = useState<string | null>(null);
  /** Name of the currently expanded tactic, or null if none is expanded */
  const [expandedTactic, setExpandedTactic] = useState<string | null>(null);

  /**
   * Memoized filtered tactic list based on search query and category selection.
   * Both filters must pass for a tactic to be included in the results.
   * Search is case-insensitive and matches against both name and description.
   */
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
      {/* Search input and category filter buttons */}
      <div className="flex flex-col sm:flex-row gap-3">
        {/* Search input with magnifying glass icon */}
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

        {/* Category filter toggle buttons.
            "All" button clears the filter. Individual category buttons toggle
            on/off: clicking an active category deselects it (returns to "All"). */}
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

      {/* Results count indicator -- pluralizes correctly for singular/plural */}
      <div className="text-sm text-muted-foreground">
        {filtered.length} tactic{filtered.length !== 1 ? 's' : ''}
      </div>

      {/* Tactic card list -- each card is expandable in accordion fashion */}
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

/* ========================================================================
 * TacticCard -- Internal expandable card for a single tactic entry
 * ======================================================================== */

/**
 * Renders a single tactic as an expandable card.
 *
 * In its collapsed state, shows the tactic name, category badge, and a
 * single-line description preview. When expanded, reveals the full signature,
 * description, example code, and related tactics.
 *
 * @param props.tactic - The tactic documentation object.
 * @param props.expanded - Whether this card is currently expanded.
 * @param props.onToggle - Callback to toggle the expanded state.
 * @returns An expandable card UI for the tactic.
 */
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
      {/* Clickable header area -- toggles expansion on click */}
      <button onClick={onToggle} className="w-full p-3 flex items-start gap-3 hover:bg-muted/30 transition-colors text-left">
        {/* Chevron indicator rotates to show expanded/collapsed state */}
        {expanded ? (
          <ChevronDown className="h-4 w-4 mt-0.5 shrink-0" />
        ) : (
          <ChevronRight className="h-4 w-4 mt-0.5 shrink-0" />
        )}
        <div className="flex-1 min-w-0">
          <div className="flex items-center gap-2 flex-wrap">
            {/* Tactic name in monospace font with primary color for emphasis */}
            <code className="font-mono font-semibold text-primary">{tactic.name}</code>
            <Badge variant="secondary" className="text-xs">
              {tactic.category}
            </Badge>
          </div>
          {/* Single-line description preview (truncated with line-clamp-1) */}
          <div className="text-sm text-muted-foreground mt-1 line-clamp-1">{tactic.description}</div>
        </div>
      </button>

      {/* Expanded detail section -- only rendered when this card is expanded */}
      {expanded && (
        <div className="border-t px-3 py-3 space-y-3 bg-muted/10">
          {/* Tactic signature (e.g., "intros x y z") */}
          <div>
            <div className="text-xs font-medium text-muted-foreground uppercase mb-1">Signature</div>
            <code className="text-sm font-mono">{tactic.signature}</code>
          </div>

          {/* Full description text */}
          <div>
            <div className="text-xs font-medium text-muted-foreground uppercase mb-1">Description</div>
            <p className="text-sm">{tactic.description}</p>
          </div>

          {/* Usage example in a monospace code block */}
          <div>
            <div className="text-xs font-medium text-muted-foreground uppercase mb-1">Example</div>
            <pre className="text-sm font-mono bg-muted p-3 rounded-md overflow-x-auto">
              <code>{tactic.example}</code>
            </pre>
          </div>

          {/* Related tactics section -- only shown if seeAlso has entries */}
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
