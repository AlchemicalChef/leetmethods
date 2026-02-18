/**
 * @module type-classifier
 *
 * Classifies Coq type strings into semantic categories for visual display.
 *
 * Since we don't have access to Coq's internal type checker on the client,
 * classification is done via pattern matching on the text representation
 * of types as reported by jsCoq's goal data.
 *
 * @see GoalsPanel - Consumes these classifications for badge display
 */

/**
 * Semantic category of a Coq type.
 *
 * - `inductive`: An inductive data type (nat, bool, list, option, etc.)
 * - `proposition`: A logical proposition (lives in Prop)
 * - `sort`: A universe/sort (Type, Prop, Set)
 * - `function`: A function type (contains ->)
 * - `dependent`: A dependent product (starts with forall)
 * - `equality`: An equality proposition (contains =)
 * - `unknown`: Could not be classified
 */
export type TypeKind =
  | 'inductive'
  | 'proposition'
  | 'sort'
  | 'function'
  | 'dependent'
  | 'equality'
  | 'unknown';

/** Known inductive type names from Coq's standard library. */
const INDUCTIVE_TYPES = new Set([
  'nat', 'bool', 'list', 'option', 'unit', 'prod', 'sum',
  'positive', 'N', 'Z', 'ascii', 'string', 'byte',
  'comparison', 'sumbool', 'sumor',
  'sigT', 'sig', 'ex', 'ex2',
  'vector', 'fin',
]);

/** Known proposition-forming types (inductive Props). */
const PROP_TYPES = new Set([
  'True', 'False', 'and', 'or', 'not', 'iff', 'eq', 'le', 'lt', 'ge', 'gt',
  'Acc', 'well_founded',
]);

/** Sort/universe names. */
const SORT_TYPES = new Set(['Prop', 'Type', 'Set', 'SProp']);

/**
 * Extracts the head type name from a type string.
 * E.g., "list nat" -> "list", "nat" -> "nat", "forall n : nat, ..." -> null
 */
function headTypeName(type: string): string | null {
  const trimmed = type.trim();
  // Match the first identifier
  const match = trimmed.match(/^([A-Za-z_][A-Za-z0-9_']*)/);
  return match ? match[1] : null;
}

/**
 * Classifies a Coq type string into a semantic category.
 *
 * The classification is based on pattern matching and known type names.
 * When multiple classifications could apply, the most specific one wins:
 * sort > dependent > equality > proposition > inductive > function > unknown
 *
 * @param type - The type string as reported by jsCoq (plain text)
 * @returns The classified TypeKind
 */
export function classifyType(type: string): TypeKind {
  const trimmed = type.trim();

  // Sort types (exact match only)
  const head = headTypeName(trimmed);
  if (head && SORT_TYPES.has(head) && trimmed.length === head.length) {
    return 'sort';
  }

  // Dependent type: starts with "forall" — must check before equality
  // because "forall n : nat, n = 0 -> P n" contains "=" but is dependent
  if (trimmed.startsWith('forall ') || trimmed.startsWith('forall(')) {
    return 'dependent';
  }

  // Equality: contains `=` at the top level (not inside parens)
  // Simple heuristic: check for ` = ` pattern
  if (/\s=\s/.test(trimmed) || /^[^(]*=/.test(trimmed)) {
    return 'equality';
  }

  // Proposition types (known logical connectives)
  if (head && PROP_TYPES.has(head)) {
    return 'proposition';
  }
  // ~ (negation notation)
  if (trimmed.startsWith('~')) {
    return 'proposition';
  }
  // /\ and \/ (conjunction/disjunction notation)
  if (trimmed.includes('/\\') || trimmed.includes('\\/')) {
    return 'proposition';
  }
  // <-> (iff notation) — check BEFORE function type so "(A <-> B)" isn't misclassified
  if (trimmed.includes('<->')) {
    return 'proposition';
  }

  // Inductive types
  if (head && INDUCTIVE_TYPES.has(head)) {
    return 'inductive';
  }

  // Function type: contains -> but not <-> (already handled above)
  if (/(?:^|[^<])->/.test(trimmed)) {
    return 'function';
  }

  return 'unknown';
}

/** Display configuration for each type kind. */
export interface TypeBadgeInfo {
  /** Short label for the badge */
  label: string;
  /** Tailwind classes for badge styling */
  className: string;
  /** Tooltip text explaining the classification */
  title: string;
}

/** Maps type kinds to their visual display configuration. */
const badgeConfig: Record<TypeKind, TypeBadgeInfo | null> = {
  inductive: {
    label: 'ind',
    className: 'bg-violet-100 text-violet-700 dark:bg-violet-900 dark:text-violet-300',
    title: 'Inductive type — can be destructed or used with induction',
  },
  proposition: {
    label: 'prop',
    className: 'bg-sky-100 text-sky-700 dark:bg-sky-900 dark:text-sky-300',
    title: 'Proposition — a logical statement (conjunction, disjunction, etc.)',
  },
  sort: {
    label: 'sort',
    className: 'bg-gray-100 text-gray-600 dark:bg-gray-800 dark:text-gray-400',
    title: 'Sort/universe — a type of types',
  },
  function: {
    label: 'fun',
    className: 'bg-amber-100 text-amber-700 dark:bg-amber-900 dark:text-amber-300',
    title: 'Function type — can be applied with apply or used with intros',
  },
  dependent: {
    label: 'dep',
    className: 'bg-emerald-100 text-emerald-700 dark:bg-emerald-900 dark:text-emerald-300',
    title: 'Dependent type (forall) — introduce with intros or apply',
  },
  equality: {
    label: 'eq',
    className: 'bg-orange-100 text-orange-700 dark:bg-orange-900 dark:text-orange-300',
    title: 'Equality — can be rewritten with rewrite, solved with reflexivity',
  },
  unknown: null,
};

/**
 * Returns the badge display info for a given type string, or null if
 * the type could not be classified into a meaningful category.
 */
export function getTypeBadge(type: string): TypeBadgeInfo | null {
  const kind = classifyType(type);
  return badgeConfig[kind];
}
