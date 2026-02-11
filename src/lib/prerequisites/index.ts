/**
 * Public API barrel file for the prerequisites system.
 *
 * Re-exports the concept registry data, prerequisite evaluation functions,
 * and all associated types. Consumers can import from `@/lib/prerequisites`
 * without needing to know the internal file structure.
 *
 * The prerequisites system allows problems to declare required knowledge
 * (tactics, lemmas, concepts, and other problems) and provides evaluation
 * logic to check which prerequisites a user has met.
 *
 * @module prerequisites
 */

export { concepts, conceptMap } from './concepts';
export type { ConceptInfo } from './concepts';
export { getPrerequisiteStatus, getUnsatisfiedCount } from './utils';
export type { PrerequisiteStatus, ProblemPrereq, ConceptPrereq } from './utils';
