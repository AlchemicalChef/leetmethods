import { describe, it, expect } from 'vitest';
import { tutorials } from './registry';

describe('tutorial registry', () => {
  it('has at least one tutorial', () => {
    expect(tutorials.length).toBeGreaterThan(0);
  });

  it('all slugs are unique', () => {
    const slugs = tutorials.map((t) => t.slug);
    expect(new Set(slugs).size).toBe(slugs.length);
  });

  it('all storage keys are unique', () => {
    const keys = tutorials.map((t) => t.storageKey);
    expect(new Set(keys).size).toBe(keys.length);
  });

  it('every tutorial has a valid completionLink', () => {
    for (const tutorial of tutorials) {
      expect(tutorial.completionLink.href).toBeTruthy();
      expect(tutorial.completionLink.label).toBeTruthy();
    }
  });
});

for (const tutorial of tutorials) {
  describe(`tutorial: ${tutorial.slug}`, () => {
    const { steps } = tutorial;

    it('has at least one step', () => {
      expect(steps.length).toBeGreaterThan(0);
    });

    it('has sequential IDs starting from 1', () => {
      const ids = steps.map((s) => s.id);
      const expected = Array.from({ length: steps.length }, (_, i) => i + 1);
      expect(ids).toEqual(expected);
    });

    it('all required fields are non-empty', () => {
      for (const step of steps) {
        expect(step.title, `step ${step.id} title`).toBeTruthy();
        expect(step.explanation, `step ${step.id} explanation`).toBeTruthy();
        expect(step.successMessage, `step ${step.id} successMessage`).toBeTruthy();
        expect(step.hint, `step ${step.id} hint`).toBeTruthy();
      }
    });

    it('exercises have prelude, template, and solution', () => {
      for (const step of steps) {
        expect(typeof step.exercise.prelude, `step ${step.id} prelude`).toBe('string');
        expect(step.exercise.template, `step ${step.id} template`).toBeTruthy();
        expect(step.exercise.solution, `step ${step.id} solution`).toBeTruthy();
      }
    });

    it('templates end with Admitted.', () => {
      for (const step of steps) {
        expect(
          step.exercise.template.trimEnd().endsWith('Admitted.'),
          `step ${step.id} template should end with Admitted. — got: "${step.exercise.template.slice(-30)}"`
        ).toBe(true);
      }
    });

    it('solutions end with Qed.', () => {
      for (const step of steps) {
        expect(
          step.exercise.solution.trimEnd().endsWith('Qed.'),
          `step ${step.id} solution should end with Qed. — got: "${step.exercise.solution.slice(-30)}"`
        ).toBe(true);
      }
    });
  });
}
