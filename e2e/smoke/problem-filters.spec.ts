import { test as baseTest, expect as baseExpect } from '@playwright/test';
import { test, expect } from '../fixtures/test-fixtures';

baseTest.describe('Problem filters (no seed)', () => {
  baseTest.beforeEach(async ({ page }) => {
    await page.goto('/problems');
  });

  baseTest('difficulty filter narrows results', async ({ page }) => {
    // Get initial count
    const showingText = page.getByText(/Showing \d+ of \d+/);
    await baseExpect(showingText).toBeVisible();
    const initialText = await showingText.textContent();
    const initialTotal = parseInt(initialText!.match(/of (\d+)/)![1]);

    // Open difficulty select — it's a combobox with "All Levels" text
    await page.getByRole('combobox').filter({ hasText: 'All Levels' }).click();

    // Select "Easy" from the dropdown portal
    await page.getByRole('option', { name: 'Easy' }).click();

    // Filtered count should be less than or equal to total
    const filteredText = await showingText.textContent();
    const filteredCount = parseInt(filteredText!.match(/Showing (\d+)/)![1]);
    baseExpect(filteredCount).toBeLessThanOrEqual(initialTotal);
    baseExpect(filteredCount).toBeGreaterThan(0);
  });

  baseTest('category filter shows matching problems', async ({ page }) => {
    // Open category select — it shows "All Categories"
    await page.getByRole('combobox').filter({ hasText: 'All Categories' }).click();

    // Select "Logic" from the dropdown
    await page.getByRole('option', { name: 'Logic' }).click();

    // Showing text should reflect filtering
    await baseExpect(page.getByText(/Showing \d+ of/)).toBeVisible();

    // Count should be less than total (there are problems in other categories)
    const showingText = await page.getByText(/Showing \d+ of/).textContent();
    const shown = parseInt(showingText!.match(/Showing (\d+)/)![1]);
    const total = parseInt(showingText!.match(/of (\d+)/)![1]);
    baseExpect(shown).toBeLessThan(total);
    baseExpect(shown).toBeGreaterThan(0);
  });
});

test.describe('Problem filters (seeded)', () => {
  test('status filter with seeded data — solved/unsolved', async ({ seededPage: page }) => {
    await page.goto('/problems');

    // Open status select — it shows "All Status"
    await page.getByRole('combobox').filter({ hasText: 'All Status' }).click();
    await page.getByRole('option', { name: 'Solved', exact: true }).click();

    // Should show exactly 3 (our seeded completions)
    await expect(page.getByText(/Showing 3 of/)).toBeVisible();

    // Switch to "Unsolved" — need to re-open the status select (now shows "Solved")
    await page.getByRole('combobox').filter({ hasText: 'Solved' }).click();
    await page.getByRole('option', { name: 'Unsolved' }).click();

    // Those 3 should be excluded — count should be total minus 3
    const showingText = await page.getByText(/Showing \d+ of/).textContent();
    const shown = parseInt(showingText!.match(/Showing (\d+)/)![1]);
    const total = parseInt(showingText!.match(/of (\d+)/)![1]);
    expect(shown).toBe(total - 3);
  });

  test('combined filters — search + status', async ({ seededPage: page }) => {
    await page.goto('/problems');

    // Search for "modus"
    await page.getByPlaceholder('Search problems...').fill('modus');

    // Select status "Solved"
    await page.getByRole('combobox').filter({ hasText: 'All Status' }).click();
    await page.getByRole('option', { name: 'Solved', exact: true }).click();

    // Only Modus Ponens should show
    await expect(page.getByText(/Showing 1 of/)).toBeVisible();
    await expect(page.getByText('Modus Ponens')).toBeVisible();
  });
});
