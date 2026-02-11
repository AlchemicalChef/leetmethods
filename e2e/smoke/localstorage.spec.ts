import { test, expect } from '../fixtures/test-fixtures';

test.describe('localStorage persistence', () => {
  test('seeded completion shows checkmarks on problems list and survives reload', async ({ seededPage: page }) => {
    await page.goto('/problems');

    // The seeded problems (modus-ponens, double-negation, and-commutative) should show as solved
    // ProblemList shows "X solved" count when completedSlugs.length > 0
    await expect(page.getByText(/3 solved/)).toBeVisible();

    // Green checkmark icons should be present (CheckCircle2 from lucide)
    // They render as SVG elements with class text-green-500
    const checkmarks = page.locator('svg.text-green-500');
    await expect(checkmarks).toHaveCount(3);

    // Reload and verify persistence
    await page.reload();
    await expect(page.getByText(/3 solved/)).toBeVisible();
    await expect(page.locator('svg.text-green-500')).toHaveCount(3);
  });

  test('seeded editor code loads in problem solver', async ({ seededPage: page }) => {
    await page.goto('/problems/modus-ponens');

    // The seeded code should appear in the CodeMirror editor
    // Desktop + mobile layout produce 2 .cm-content elements; use first()
    const editorContent = page.locator('.cm-content').first();
    await expect(editorContent).toContainText('modus_ponens');
    await expect(editorContent).toContainText('apply HPQ');
  });
});
