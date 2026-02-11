import { test, expect } from '@playwright/test';

test.describe('Problems list page', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/problems');
  });

  test('loads with search input and problem cards', async ({ page }) => {
    await expect(page.getByPlaceholder('Search problems...')).toBeVisible();
    // At least one problem card should be visible
    await expect(page.getByRole('heading', { name: /Problems/i }).first()).toBeVisible();
    // Verify there are problem links
    const problemLinks = page.locator('a[href^="/problems/"]').filter({ hasNot: page.locator('a[href="/problems/custom/create"]') });
    await expect(problemLinks.first()).toBeVisible();
  });

  test('search filter narrows results', async ({ page }) => {
    const searchInput = page.getByPlaceholder('Search problems...');
    await searchInput.fill('modus');

    // Should show "Modus Ponens" in results
    await expect(page.getByText('Modus Ponens')).toBeVisible();

    // The "Showing X of Y" text should reflect filtering
    await expect(page.getByText(/Showing \d+ of/)).toBeVisible();
  });

  test('clicking a problem card navigates to /problems/[slug]', async ({ page }) => {
    // Click on the first problem link
    const firstProblem = page.locator('a[href^="/problems/"]').filter({ hasNotText: 'Browse Problems' }).filter({ hasNotText: 'Create Problem' }).first();
    await firstProblem.click();
    await expect(page).toHaveURL(/\/problems\/.+/);
  });
});
