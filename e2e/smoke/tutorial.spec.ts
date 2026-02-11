import { test, expect } from '@playwright/test';

test.describe('Tutorial page', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/tutorial/basics');
    // Wait for hydration — TutorialPage shows a spinner until useHydrated() returns true
    await page.getByText(/Step 1:/).waitFor({ state: 'visible' });
  });

  test('loads with step title, explanation, and editor', async ({ page }) => {
    // Title
    await expect(page.getByRole('heading', { name: /Tutorial: Basics/i })).toBeVisible();

    // Step title (Step 1: ...)
    await expect(page.getByText(/Step 1:/)).toBeVisible();

    // CodeMirror editor
    await expect(page.locator('.cm-editor')).toBeVisible();
  });

  test('step navigation: Next/Previous buttons change step content', async ({ page }) => {
    // The TutorialPage "Next Step" nav button uses exact "Next Step" text (capital S).
    // EditorToolbar has a separate "Next step" button (lowercase s, aria-label).
    // Use exact text match to target the navigation button.
    await page.getByRole('button', { name: 'Next Step', exact: true }).click();

    // Step 2 should now be visible
    await expect(page.getByText(/Step 2:/)).toBeVisible();

    // Click "Previous" — use exact match to avoid matching EditorToolbar's "Previous step" button
    await page.getByRole('button', { name: 'Previous', exact: true }).click();
    await expect(page.getByText(/Step 1:/)).toBeVisible();
  });

  test('step progress persists to localStorage and survives reload', async ({ page }) => {
    // Navigate to step 2
    await page.getByRole('button', { name: 'Next Step', exact: true }).click();
    await expect(page.getByText(/Step 2:/)).toBeVisible();

    // Verify localStorage was updated
    const stored = await page.evaluate(() =>
      localStorage.getItem('leetmethods-tutorial-progress')
    );
    expect(stored).toBe('1'); // 0-indexed step

    // Reload and verify step 2 is restored
    await page.reload();
    await expect(page.getByText(/Step 2:/)).toBeVisible();
  });

  test('step indicator dots allow jumping to specific steps', async ({ page }) => {
    // Step indicator dots are round buttons with numbers (1, 2, 3, ...)
    const dot3 = page.locator('button.rounded-full').filter({ hasText: '3' });
    await dot3.click();

    await expect(page.getByText(/Step 3:/)).toBeVisible();
  });
});
