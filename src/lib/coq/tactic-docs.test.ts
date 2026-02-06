import { describe, it, expect } from 'vitest';
import { tacticDocs, tacticDocMap, type TacticDoc } from './tactic-docs';

// Known categories for validation
const KNOWN_CATEGORIES = [
  'Introduction',
  'Application',
  'Automation',
  'Rewriting',
  'Simplification',
  'Case Analysis',
  'Logic',
  'Assertion',
  'Context Management',
  'Computation',
  'Arithmetic',
  'Tacticals',
  'Advanced',
] as const;

describe('tacticDocs array', () => {
  it('has entries (length > 0)', () => {
    expect(tacticDocs.length).toBeGreaterThan(0);
  });

  it('every entry has all required fields', () => {
    tacticDocs.forEach((doc, index) => {
      expect(doc, `Entry at index ${index} should be an object`).toBeDefined();
      expect(doc.name, `Entry at index ${index} should have 'name'`).toBeDefined();
      expect(doc.category, `Entry at index ${index} should have 'category'`).toBeDefined();
      expect(doc.signature, `Entry at index ${index} should have 'signature'`).toBeDefined();
      expect(doc.description, `Entry at index ${index} should have 'description'`).toBeDefined();
      expect(doc.example, `Entry at index ${index} should have 'example'`).toBeDefined();
      expect(doc.seeAlso, `Entry at index ${index} should have 'seeAlso'`).toBeDefined();
    });
  });

  it('every name is a non-empty string', () => {
    tacticDocs.forEach((doc, index) => {
      expect(typeof doc.name, `Entry at index ${index} name should be string`).toBe('string');
      expect(doc.name.length, `Entry at index ${index} name should not be empty`).toBeGreaterThan(0);
      expect(doc.name.trim().length, `Entry at index ${index} name should not be whitespace only`).toBeGreaterThan(0);
    });
  });

  it('every category is a non-empty string', () => {
    tacticDocs.forEach((doc, index) => {
      expect(typeof doc.category, `Entry at index ${index} (${doc.name}) category should be string`).toBe('string');
      expect(doc.category.length, `Entry at index ${index} (${doc.name}) category should not be empty`).toBeGreaterThan(0);
      expect(doc.category.trim().length, `Entry at index ${index} (${doc.name}) category should not be whitespace only`).toBeGreaterThan(0);
    });
  });

  it('every signature is a non-empty string', () => {
    tacticDocs.forEach((doc, index) => {
      expect(typeof doc.signature, `Entry at index ${index} (${doc.name}) signature should be string`).toBe('string');
      expect(doc.signature.length, `Entry at index ${index} (${doc.name}) signature should not be empty`).toBeGreaterThan(0);
      expect(doc.signature.trim().length, `Entry at index ${index} (${doc.name}) signature should not be whitespace only`).toBeGreaterThan(0);
    });
  });

  it('every description is a non-empty string', () => {
    tacticDocs.forEach((doc, index) => {
      expect(typeof doc.description, `Entry at index ${index} (${doc.name}) description should be string`).toBe('string');
      expect(doc.description.length, `Entry at index ${index} (${doc.name}) description should not be empty`).toBeGreaterThan(0);
      expect(doc.description.trim().length, `Entry at index ${index} (${doc.name}) description should not be whitespace only`).toBeGreaterThan(0);
    });
  });

  it('every example is a non-empty string', () => {
    tacticDocs.forEach((doc, index) => {
      expect(typeof doc.example, `Entry at index ${index} (${doc.name}) example should be string`).toBe('string');
      expect(doc.example.length, `Entry at index ${index} (${doc.name}) example should not be empty`).toBeGreaterThan(0);
      expect(doc.example.trim().length, `Entry at index ${index} (${doc.name}) example should not be whitespace only`).toBeGreaterThan(0);
    });
  });

  it('every seeAlso is an array', () => {
    tacticDocs.forEach((doc, index) => {
      expect(Array.isArray(doc.seeAlso), `Entry at index ${index} (${doc.name}) seeAlso should be an array`).toBe(true);
    });
  });

  it('every seeAlso array contains only strings', () => {
    tacticDocs.forEach((doc, index) => {
      doc.seeAlso.forEach((ref, refIndex) => {
        expect(typeof ref, `Entry at index ${index} (${doc.name}) seeAlso[${refIndex}] should be string`).toBe('string');
        expect(ref.length, `Entry at index ${index} (${doc.name}) seeAlso[${refIndex}] should not be empty`).toBeGreaterThan(0);
      });
    });
  });

  it('all tactic names are unique', () => {
    const names = tacticDocs.map(doc => doc.name);
    const uniqueNames = new Set(names);
    expect(uniqueNames.size, 'All tactic names should be unique').toBe(names.length);
  });

  it('has expected minimum number of tactics (55+)', () => {
    expect(tacticDocs.length).toBeGreaterThanOrEqual(55);
  });

  it('contains known essential tactics', () => {
    const essentialTactics = [
      'intros', 'intro', 'apply', 'exact', 'assumption',
      'reflexivity', 'symmetry', 'rewrite', 'destruct', 'induction',
      'split', 'left', 'right', 'exists', 'auto', 'lia'
    ];

    const tacticNames = new Set(tacticDocs.map(doc => doc.name));

    essentialTactics.forEach(tacticName => {
      expect(tacticNames.has(tacticName), `Should include essential tactic: ${tacticName}`).toBe(true);
    });
  });
});

describe('tacticDocMap', () => {
  it('is a Map instance', () => {
    expect(tacticDocMap instanceof Map, 'tacticDocMap should be a Map instance').toBe(true);
  });

  it('has the same size as tacticDocs array', () => {
    expect(tacticDocMap.size).toBe(tacticDocs.length);
  });

  it('can look up "intros" tactic', () => {
    const doc = tacticDocMap.get('intros');
    expect(doc).toBeDefined();
    expect(doc?.name).toBe('intros');
    expect(doc?.category).toBe('Introduction');
    expect(doc?.signature).toBeTruthy();
    expect(doc?.description).toBeTruthy();
    expect(doc?.example).toBeTruthy();
    expect(Array.isArray(doc?.seeAlso)).toBe(true);
  });

  it('can look up "apply" tactic', () => {
    const doc = tacticDocMap.get('apply');
    expect(doc).toBeDefined();
    expect(doc?.name).toBe('apply');
    expect(doc?.category).toBe('Application');
    expect(doc?.signature).toBeTruthy();
    expect(doc?.description).toBeTruthy();
    expect(doc?.example).toBeTruthy();
  });

  it('can look up "lia" tactic', () => {
    const doc = tacticDocMap.get('lia');
    expect(doc).toBeDefined();
    expect(doc?.name).toBe('lia');
    expect(doc?.category).toBe('Arithmetic');
    expect(doc?.signature).toBeTruthy();
    expect(doc?.description).toBeTruthy();
    expect(doc?.example).toBeTruthy();
  });

  it('can look up "destruct" tactic', () => {
    const doc = tacticDocMap.get('destruct');
    expect(doc).toBeDefined();
    expect(doc?.name).toBe('destruct');
    expect(doc?.category).toBe('Case Analysis');
    expect(doc?.signature).toBeTruthy();
    expect(doc?.description).toBeTruthy();
    expect(doc?.example).toBeTruthy();
  });

  it('returns undefined for unknown tactic name', () => {
    const doc = tacticDocMap.get('nonexistent_tactic_xyz_12345');
    expect(doc).toBeUndefined();
  });

  it('returns undefined for empty string lookup', () => {
    const doc = tacticDocMap.get('');
    expect(doc).toBeUndefined();
  });

  it('each map entry matches the corresponding array entry', () => {
    tacticDocs.forEach(doc => {
      const mapDoc = tacticDocMap.get(doc.name);
      expect(mapDoc).toBeDefined();
      expect(mapDoc).toBe(doc); // Should be the same object reference
    });
  });

  it('map keys match array names exactly', () => {
    const arrayNames = new Set(tacticDocs.map(doc => doc.name));
    const mapKeys = new Set(tacticDocMap.keys());

    expect(mapKeys.size).toBe(arrayNames.size);
    arrayNames.forEach(name => {
      expect(mapKeys.has(name), `Map should have key: ${name}`).toBe(true);
    });
  });
});

describe('Category coverage', () => {
  it('every entry has a recognized category from the known list', () => {
    const knownCategoriesSet = new Set(KNOWN_CATEGORIES);

    tacticDocs.forEach((doc, index) => {
      expect(
        knownCategoriesSet.has(doc.category as string),
        `Entry at index ${index} (${doc.name}) has unrecognized category: "${doc.category}"`
      ).toBe(true);
    });
  });

  it('each known category has at least one tactic', () => {
    const categoryCounts = new Map<string, number>();

    // Count tactics per category
    tacticDocs.forEach(doc => {
      categoryCounts.set(doc.category, (categoryCounts.get(doc.category) || 0) + 1);
    });

    // Verify each known category has at least one tactic
    KNOWN_CATEGORIES.forEach(category => {
      const count = categoryCounts.get(category) || 0;
      expect(count, `Category "${category}" should have at least one tactic`).toBeGreaterThan(0);
    });
  });

  it('Introduction category contains intro and intros', () => {
    const introTactics = tacticDocs.filter(doc => doc.category === 'Introduction');
    const introTacticNames = new Set(introTactics.map(doc => doc.name));

    expect(introTacticNames.has('intro')).toBe(true);
    expect(introTacticNames.has('intros')).toBe(true);
  });

  it('Automation category contains auto and eauto', () => {
    const autoTactics = tacticDocs.filter(doc => doc.category === 'Automation');
    const autoTacticNames = new Set(autoTactics.map(doc => doc.name));

    expect(autoTacticNames.has('auto')).toBe(true);
    expect(autoTacticNames.has('eauto')).toBe(true);
  });

  it('Arithmetic category contains lia, ring, and related tactics', () => {
    const arithTactics = tacticDocs.filter(doc => doc.category === 'Arithmetic');
    const arithTacticNames = new Set(arithTactics.map(doc => doc.name));

    expect(arithTacticNames.has('lia')).toBe(true);
    expect(arithTacticNames.has('ring')).toBe(true);
    expect(arithTactics.length).toBeGreaterThan(0);
  });

  it('Logic category contains split, left, right, exists', () => {
    const logicTactics = tacticDocs.filter(doc => doc.category === 'Logic');
    const logicTacticNames = new Set(logicTactics.map(doc => doc.name));

    expect(logicTacticNames.has('split')).toBe(true);
    expect(logicTacticNames.has('left')).toBe(true);
    expect(logicTacticNames.has('right')).toBe(true);
    expect(logicTacticNames.has('exists')).toBe(true);
  });

  it('Tacticals category contains repeat, try, do', () => {
    const tacticalTactics = tacticDocs.filter(doc => doc.category === 'Tacticals');
    const tacticalTacticNames = new Set(tacticalTactics.map(doc => doc.name));

    expect(tacticalTacticNames.has('repeat')).toBe(true);
    expect(tacticalTacticNames.has('try')).toBe(true);
    expect(tacticalTacticNames.has('do')).toBe(true);
  });

  it('no category is empty', () => {
    const categoryCounts = new Map<string, number>();

    tacticDocs.forEach(doc => {
      categoryCounts.set(doc.category, (categoryCounts.get(doc.category) || 0) + 1);
    });

    categoryCounts.forEach((count, category) => {
      expect(count, `Category "${category}" should not be empty`).toBeGreaterThan(0);
    });
  });
});

describe('seeAlso cross-reference integrity', () => {
  it('identifies all missing tactic references for documentation', () => {
    const allTacticNames = new Set(tacticDocs.map(doc => doc.name));
    const missingReferences = new Set<string>();

    tacticDocs.forEach((doc) => {
      doc.seeAlso.forEach((ref) => {
        if (!allTacticNames.has(ref)) {
          missingReferences.add(ref);
        }
      });
    });

    // This test documents which tactics are referenced but not yet documented
    // If this test fails, it means new missing references were added
    const expectedMissingReferences = [
      'Admitted',
      'absurd',
      'apply .. in',
      'cbn',
      'eapply',
      'easy',
      'eexists',
      'fix',
      'intuition',
      'lra',
      'typeclasses eauto'
    ];

    const missing = Array.from(missingReferences).sort();

    // If you're adding new tactics, update expectedMissingReferences if needed
    expect(missing,
      `Missing references found. These tactics are referenced but not documented:\n${missing.map(m => `  - ${m}`).join('\n')}\n\n` +
      `If these are intentional (e.g., special syntax like "apply .. in"), add them to expectedMissingReferences.\n` +
      `Otherwise, add documentation for these tactics.`
    ).toEqual(expectedMissingReferences);
  });

  it('no tactic references itself in seeAlso', () => {
    tacticDocs.forEach((doc, index) => {
      expect(
        doc.seeAlso.includes(doc.name),
        `Entry at index ${index} (${doc.name}) should not reference itself in seeAlso`
      ).toBe(false);
    });
  });

  it('seeAlso arrays do not contain duplicate references', () => {
    tacticDocs.forEach((doc, index) => {
      const uniqueRefs = new Set(doc.seeAlso);
      expect(
        uniqueRefs.size,
        `Entry at index ${index} (${doc.name}) seeAlso should not contain duplicates`
      ).toBe(doc.seeAlso.length);
    });
  });

  it('intros references intro in seeAlso', () => {
    const introsDoc = tacticDocMap.get('intros');
    expect(introsDoc).toBeDefined();
    expect(introsDoc?.seeAlso.includes('intro')).toBe(true);
  });

  it('apply references exact in seeAlso', () => {
    const applyDoc = tacticDocMap.get('apply');
    expect(applyDoc).toBeDefined();
    expect(applyDoc?.seeAlso.includes('exact')).toBe(true);
  });

  it('reflexivity has symmetry and transitivity in seeAlso', () => {
    const reflexivityDoc = tacticDocMap.get('reflexivity');
    expect(reflexivityDoc).toBeDefined();
    expect(reflexivityDoc?.seeAlso).toContain('symmetry');
    expect(reflexivityDoc?.seeAlso).toContain('transitivity');
  });

  it('destruct and induction reference each other', () => {
    const destructDoc = tacticDocMap.get('destruct');
    const inductionDoc = tacticDocMap.get('induction');

    expect(destructDoc).toBeDefined();
    expect(inductionDoc).toBeDefined();
    expect(destructDoc?.seeAlso).toContain('induction');
    expect(inductionDoc?.seeAlso).toContain('destruct');
  });
});

describe('Data structure integrity', () => {
  it('tacticDocs is an array', () => {
    expect(Array.isArray(tacticDocs)).toBe(true);
  });

  it('tacticDocs is not empty', () => {
    expect(tacticDocs.length).toBeGreaterThan(0);
  });

  it('tacticDocMap is not empty', () => {
    expect(tacticDocMap.size).toBeGreaterThan(0);
  });

  it('all entries conform to TacticDoc interface', () => {
    tacticDocs.forEach((doc, index) => {
      // Type structure validation
      const requiredKeys: (keyof TacticDoc)[] = [
        'name',
        'category',
        'signature',
        'description',
        'example',
        'seeAlso'
      ];

      requiredKeys.forEach(key => {
        expect(
          key in doc,
          `Entry at index ${index} (${doc.name}) should have property: ${key}`
        ).toBe(true);
      });

      // Type checking
      expect(typeof doc.name).toBe('string');
      expect(typeof doc.category).toBe('string');
      expect(typeof doc.signature).toBe('string');
      expect(typeof doc.description).toBe('string');
      expect(typeof doc.example).toBe('string');
      expect(Array.isArray(doc.seeAlso)).toBe(true);
    });
  });
});

describe('Content quality checks', () => {
  it('examples contain "Proof" keyword', () => {
    const tacticsRequiringProof = tacticDocs.filter(doc =>
      doc.name !== 'admit' && doc.name !== 'give_up'
    );

    tacticsRequiringProof.forEach(doc => {
      if (doc.example.includes('Goal')) {
        expect(
          doc.example.includes('Proof'),
          `${doc.name} example should contain "Proof" keyword`
        ).toBe(true);
      }
    });
  });

  it('descriptions are sufficiently detailed (at least 50 characters)', () => {
    tacticDocs.forEach((doc, index) => {
      expect(
        doc.description.length,
        `Entry at index ${index} (${doc.name}) description should be at least 50 characters`
      ).toBeGreaterThanOrEqual(50);
    });
  });

  it('examples are sufficiently detailed (at least 20 characters)', () => {
    tacticDocs.forEach((doc, index) => {
      expect(
        doc.example.length,
        `Entry at index ${index} (${doc.name}) example should be at least 20 characters`
      ).toBeGreaterThanOrEqual(20);
    });
  });

  it('no description ends with incomplete sentence', () => {
    tacticDocs.forEach((doc, index) => {
      const lastChar = doc.description.trim().slice(-1);
      expect(
        ['.', '!', '?'].includes(lastChar) || doc.description.includes('\n'),
        `Entry at index ${index} (${doc.name}) description should end with proper punctuation`
      ).toBe(true);
    });
  });
});

describe('Specific tactic validations', () => {
  it('intros tactic has correct structure', () => {
    const intros = tacticDocMap.get('intros');
    expect(intros).toBeDefined();
    expect(intros?.name).toBe('intros');
    expect(intros?.category).toBe('Introduction');
    expect(intros?.description).toContain('hypotheses');
    expect(intros?.example).toContain('intros');
  });

  it('apply tactic has correct structure', () => {
    const apply = tacticDocMap.get('apply');
    expect(apply).toBeDefined();
    expect(apply?.name).toBe('apply');
    expect(apply?.category).toBe('Application');
    expect(apply?.signature).toContain('apply');
    expect(apply?.description.toLowerCase()).toContain('goal');
  });

  it('lia tactic has correct structure', () => {
    const lia = tacticDocMap.get('lia');
    expect(lia).toBeDefined();
    expect(lia?.name).toBe('lia');
    expect(lia?.category).toBe('Arithmetic');
    expect(lia?.description.toLowerCase()).toContain('linear');
    expect(lia?.description.toLowerCase()).toContain('arithmetic');
  });

  it('omega tactic mentions deprecation', () => {
    const omega = tacticDocMap.get('omega');
    if (omega) {
      expect(omega.description.toLowerCase()).toContain('deprecated');
      expect(omega.seeAlso).toContain('lia');
    }
  });

  it('admit and give_up are in Advanced category', () => {
    const admit = tacticDocMap.get('admit');
    const giveUp = tacticDocMap.get('give_up');

    expect(admit?.category).toBe('Advanced');
    expect(giveUp?.category).toBe('Advanced');
  });

  it('constructor and econstructor reference each other', () => {
    const constructor = tacticDocMap.get('constructor');
    const econstructor = tacticDocMap.get('econstructor');

    expect(constructor).toBeDefined();
    expect(econstructor).toBeDefined();
    expect(econstructor?.seeAlso).toContain('constructor');
  });
});
