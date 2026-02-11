/**
 * Pre-built localStorage payloads matching Zustand persist schemas.
 * These are injected via page.evaluate() before navigating to test pages.
 */

function todayString(): string {
  const d = new Date();
  const year = d.getFullYear();
  const month = String(d.getMonth() + 1).padStart(2, '0');
  const day = String(d.getDate()).padStart(2, '0');
  return `${year}-${month}-${day}`;
}

/** progressStore — leetmethods-progress, version 3 */
export function progressSeed() {
  return JSON.stringify({
    state: {
      progress: {
        'modus-ponens': {
          slug: 'modus-ponens',
          completed: true,
          completedAt: Date.now() - 86400000,
          attempts: 2,
          hintsUsed: 1,
          solveStartedAt: null,
          solveDurationMs: 120000,
          srs: null,
          reviewAttempts: 0,
          reviewHintsUsed: 0,
          isReviewing: false,
        },
        'double-negation': {
          slug: 'double-negation',
          completed: true,
          completedAt: Date.now() - 172800000,
          attempts: 3,
          hintsUsed: 0,
          solveStartedAt: null,
          solveDurationMs: 90000,
          srs: null,
          reviewAttempts: 0,
          reviewHintsUsed: 0,
          isReviewing: false,
        },
        'and-commutative': {
          slug: 'and-commutative',
          completed: true,
          completedAt: Date.now() - 259200000,
          attempts: 1,
          hintsUsed: 0,
          solveStartedAt: null,
          solveDurationMs: 60000,
          srs: null,
          reviewAttempts: 0,
          reviewHintsUsed: 0,
          isReviewing: false,
        },
      },
      streakData: {
        currentStreak: 1,
        longestStreak: 3,
        lastSolveDate: todayString(),
      },
    },
    version: 3,
  });
}

/**
 * editorStore — leetmethods-editor
 * The store only persists `savedCodes` via partialize.
 */
export function editorSeed() {
  return JSON.stringify({
    state: {
      savedCodes: {
        'modus-ponens':
          'Theorem modus_ponens : forall P Q : Prop, P -> (P -> Q) -> Q.\nProof.\n  intros P Q HP HPQ.\n  apply HPQ.\n  exact HP.\nQed.',
      },
    },
    version: 0,
  });
}

/** progressStore with SRS fields populated and nextReviewAt in the past */
export function progressSeedWithSrs() {
  const pastTimestamp = Date.now() - 86400000;
  return JSON.stringify({
    state: {
      progress: {
        'modus-ponens': {
          slug: 'modus-ponens',
          completed: true,
          completedAt: Date.now() - 86400000,
          attempts: 2,
          hintsUsed: 1,
          solveStartedAt: null,
          solveDurationMs: 120000,
          srs: { interval: 1, easeFactor: 2.5, nextReviewAt: pastTimestamp, reviewCount: 1, lastReviewQuality: 5 },
          reviewAttempts: 0,
          reviewHintsUsed: 0,
          isReviewing: false,
        },
        'double-negation': {
          slug: 'double-negation',
          completed: true,
          completedAt: Date.now() - 172800000,
          attempts: 3,
          hintsUsed: 0,
          solveStartedAt: null,
          solveDurationMs: 90000,
          srs: { interval: 1, easeFactor: 2.5, nextReviewAt: pastTimestamp, reviewCount: 1, lastReviewQuality: 5 },
          reviewAttempts: 0,
          reviewHintsUsed: 0,
          isReviewing: false,
        },
        'and-commutative': {
          slug: 'and-commutative',
          completed: true,
          completedAt: Date.now() - 259200000,
          attempts: 1,
          hintsUsed: 0,
          solveStartedAt: null,
          solveDurationMs: 60000,
          srs: { interval: 1, easeFactor: 2.5, nextReviewAt: pastTimestamp, reviewCount: 1, lastReviewQuality: 5 },
          reviewAttempts: 0,
          reviewHintsUsed: 0,
          isReviewing: false,
        },
      },
      streakData: {
        currentStreak: 1,
        longestStreak: 3,
        lastSolveDate: todayString(),
      },
    },
    version: 3,
  });
}

/** Tutorial step progress — plain string (not JSON), set directly by TutorialPage */
export const tutorialProgressValue = '2';
