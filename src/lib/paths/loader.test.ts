import { describe, it, expect } from 'vitest';
import { getAllPaths, getPathBySlug } from './loader';

describe('getAllPaths', () => {
  it('should return an array', () => {
    const paths = getAllPaths();
    expect(Array.isArray(paths)).toBe(true);
  });

  it('should return exactly 8 paths', () => {
    const paths = getAllPaths();
    expect(paths).toHaveLength(8);
  });

  it('should ensure every path has all required fields', () => {
    const paths = getAllPaths();

    paths.forEach((path) => {
      expect(path).toHaveProperty('slug');
      expect(path).toHaveProperty('title');
      expect(path).toHaveProperty('description');
      expect(path).toHaveProperty('difficulty');
      expect(path).toHaveProperty('icon');
      expect(path).toHaveProperty('steps');

      // Verify types
      expect(typeof path.slug).toBe('string');
      expect(typeof path.title).toBe('string');
      expect(typeof path.description).toBe('string');
      expect(typeof path.difficulty).toBe('string');
      expect(typeof path.icon).toBe('string');
      expect(Array.isArray(path.steps)).toBe(true);
    });
  });

  it('should have unique slugs across all paths', () => {
    const paths = getAllPaths();
    const slugs = paths.map((path) => path.slug);
    const uniqueSlugs = new Set(slugs);

    expect(uniqueSlugs.size).toBe(slugs.length);
  });

  it('should return non-empty string values for required fields', () => {
    const paths = getAllPaths();

    paths.forEach((path) => {
      expect(path.slug.length).toBeGreaterThan(0);
      expect(path.title.length).toBeGreaterThan(0);
      expect(path.description.length).toBeGreaterThan(0);
      expect(path.icon.length).toBeGreaterThan(0);
    });
  });
});

describe('getPathBySlug', () => {
  it('should return correct path for "foundations-of-logic"', () => {
    const path = getPathBySlug('foundations-of-logic');

    expect(path).not.toBeNull();
    expect(path?.slug).toBe('foundations-of-logic');
    expect(path?.title).toBe('Foundations of Logic');
    expect(path?.difficulty).toBe('beginner');
    expect(path?.icon).toBe('🧠');
  });

  it('should return correct path for "mastering-induction"', () => {
    const path = getPathBySlug('mastering-induction');

    expect(path).not.toBeNull();
    expect(path?.slug).toBe('mastering-induction');
    expect(path?.title).toBe('Mastering Induction');
    expect(path?.difficulty).toBe('intermediate');
    expect(path?.icon).toBe('🔄');
  });

  it('should return correct path for "reasoning-about-data"', () => {
    const path = getPathBySlug('reasoning-about-data');

    expect(path).not.toBeNull();
    expect(path?.slug).toBe('reasoning-about-data');
    expect(path?.title).toBe('Reasoning About Data');
    expect(path?.difficulty).toBe('advanced');
    expect(path?.icon).toBe('🌳');
  });

  it('should return null for unknown slug', () => {
    const path = getPathBySlug('non-existent-path');
    expect(path).toBeNull();
  });

  it('should return null for empty string', () => {
    const path = getPathBySlug('');
    expect(path).toBeNull();
  });

  it('should return null for slug with different casing', () => {
    const path = getPathBySlug('FOUNDATIONS-OF-LOGIC');
    expect(path).toBeNull();
  });

  it('should return null for slug with whitespace', () => {
    const path = getPathBySlug(' foundations-of-logic ');
    expect(path).toBeNull();
  });

  it('should return null for partial slug match', () => {
    const path = getPathBySlug('foundations');
    expect(path).toBeNull();
  });
});

describe('Data Integrity', () => {
  describe('Path Steps', () => {
    it('should ensure each path has at least one step', () => {
      const paths = getAllPaths();

      paths.forEach((path) => {
        expect(path.steps.length).toBeGreaterThan(0);
      });
    });

    it('should ensure each step has problemSlug, title, and description', () => {
      const paths = getAllPaths();

      paths.forEach((path) => {
        path.steps.forEach((step) => {
          expect(step).toHaveProperty('problemSlug');
          expect(step).toHaveProperty('title');
          expect(step).toHaveProperty('description');

          // Verify types
          expect(typeof step.problemSlug).toBe('string');
          expect(typeof step.title).toBe('string');
          expect(typeof step.description).toBe('string');
        });
      });
    });

    it('should ensure each step has non-empty field values', () => {
      const paths = getAllPaths();

      paths.forEach((path) => {
        path.steps.forEach((step) => {
          expect(step.problemSlug.length).toBeGreaterThan(0);
          expect(step.title.length).toBeGreaterThan(0);
          expect(step.description.length).toBeGreaterThan(0);
        });
      });
    });

    it('should have unique problem slugs across all paths', () => {
      const paths = getAllPaths();
      const allProblemSlugs: string[] = [];

      paths.forEach((path) => {
        path.steps.forEach((step) => {
          allProblemSlugs.push(step.problemSlug);
        });
      });

      const uniqueProblemSlugs = new Set(allProblemSlugs);
      expect(uniqueProblemSlugs.size).toBe(allProblemSlugs.length);
    });
  });

  describe('Difficulty Values', () => {
    it('should only have valid difficulty values', () => {
      const paths = getAllPaths();
      const validDifficulties = ['beginner', 'intermediate', 'advanced'];

      paths.forEach((path) => {
        expect(validDifficulties).toContain(path.difficulty);
      });
    });

    it('should have at least one path of each difficulty level', () => {
      const paths = getAllPaths();
      const difficulties = paths.map((path) => path.difficulty);

      expect(difficulties).toContain('beginner');
      expect(difficulties).toContain('intermediate');
      expect(difficulties).toContain('advanced');
    });
  });

  describe('Icons', () => {
    it('should ensure all paths have non-empty icons', () => {
      const paths = getAllPaths();

      paths.forEach((path) => {
        expect(path.icon).toBeTruthy();
        expect(path.icon.length).toBeGreaterThan(0);
      });
    });

    it('should have unique icons across all paths', () => {
      const paths = getAllPaths();
      const icons = paths.map((path) => path.icon);
      const uniqueIcons = new Set(icons);

      expect(uniqueIcons.size).toBe(icons.length);
    });
  });

  describe('Slug Format', () => {
    it('should ensure all path slugs use kebab-case format', () => {
      const paths = getAllPaths();
      const kebabCaseRegex = /^[a-z0-9]+(?:-[a-z0-9]+)*$/;

      paths.forEach((path) => {
        expect(path.slug).toMatch(kebabCaseRegex);
      });
    });

    it('should ensure all problem slugs use kebab-case format', () => {
      const paths = getAllPaths();
      const kebabCaseRegex = /^[a-z0-9]+(?:-[a-z0-9]+)*$/;

      paths.forEach((path) => {
        path.steps.forEach((step) => {
          expect(step.problemSlug).toMatch(kebabCaseRegex);
        });
      });
    });

    it('should not have any slugs with spaces', () => {
      const paths = getAllPaths();

      paths.forEach((path) => {
        expect(path.slug).not.toContain(' ');

        path.steps.forEach((step) => {
          expect(step.problemSlug).not.toContain(' ');
        });
      });
    });

    it('should not have any uppercase letters in slugs', () => {
      const paths = getAllPaths();

      paths.forEach((path) => {
        expect(path.slug).toBe(path.slug.toLowerCase());

        path.steps.forEach((step) => {
          expect(step.problemSlug).toBe(step.problemSlug.toLowerCase());
        });
      });
    });
  });

  describe('Expected Path Structure', () => {
    it('should have "boolean-basics" as the first path', () => {
      const paths = getAllPaths();
      expect(paths[0].slug).toBe('boolean-basics');
      expect(paths[0].difficulty).toBe('beginner');
    });

    it('should have "foundations-of-logic" as the second path', () => {
      const paths = getAllPaths();
      expect(paths[1].slug).toBe('foundations-of-logic');
      expect(paths[1].difficulty).toBe('beginner');
    });

    it('should have "introduction-to-induction" as the third path', () => {
      const paths = getAllPaths();
      expect(paths[2].slug).toBe('introduction-to-induction');
      expect(paths[2].difficulty).toBe('beginner');
    });
  });

  describe('Reference Integrity', () => {
    it('should return the same array reference on multiple calls', () => {
      const paths1 = getAllPaths();
      const paths2 = getAllPaths();

      expect(paths1).toBe(paths2);
    });

    it('should return path object with consistent properties', () => {
      const path1 = getPathBySlug('foundations-of-logic');
      const path2 = getPathBySlug('foundations-of-logic');

      expect(path1).toEqual(path2);
    });
  });

  describe('Step Count Validation', () => {
    it('should have expected number of steps in "foundations-of-logic"', () => {
      const path = getPathBySlug('foundations-of-logic');
      expect(path?.steps.length).toBeGreaterThanOrEqual(4);
    });

    it('should have expected number of steps in "mastering-induction"', () => {
      const path = getPathBySlug('mastering-induction');
      expect(path?.steps.length).toBeGreaterThanOrEqual(4);
    });

    it('should have expected number of steps in "reasoning-about-data"', () => {
      const path = getPathBySlug('reasoning-about-data');
      expect(path?.steps.length).toBeGreaterThanOrEqual(5);
    });
  });
});
