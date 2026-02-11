import { test, expect } from '@playwright/test';

test.describe('Mobile layout', () => {
  test.beforeEach(async ({ page }) => {
    // Set mobile viewport before any navigation
    await page.setViewportSize({ width: 375, height: 812 });
  });

  test('mobile nav menu opens with links', async ({ page }) => {
    await page.goto('/');

    // Hamburger menu should be visible on mobile
    const hamburger = page.getByLabel('Toggle menu');
    await expect(hamburger).toBeVisible();

    // Open mobile menu
    await hamburger.click();

    // Mobile menu links should appear
    await expect(page.getByRole('link', { name: /Tutorial/i }).first()).toBeVisible();
    await expect(page.getByRole('link', { name: 'Problems', exact: true })).toBeVisible();
    await expect(page.getByRole('link', { name: 'Learn' })).toBeVisible();
    await expect(page.getByRole('link', { name: 'Stats' })).toBeVisible();
  });

  test('mobile menu navigation works', async ({ page }) => {
    await page.goto('/');

    await page.getByLabel('Toggle menu').click();
    await page.getByRole('link', { name: 'Learn' }).click();

    await expect(page).toHaveURL('/learn');
    // Menu should close after navigation
    await expect(page.getByRole('heading', { name: 'Learn Coq' })).toBeVisible();
  });

  test('problem page renders editor on mobile', async ({ page }) => {
    await page.goto('/problems/modus-ponens');

    // Title should be visible
    await expect(page.getByRole('heading', { name: /Modus Ponens/i })).toBeVisible();

    // On mobile, the lg:hidden container is visible — find the editor inside it
    const mobileLayout = page.locator('.lg\\:hidden');
    await expect(mobileLayout.locator('.cm-editor').first()).toBeVisible();
  });

  test('goals panel collapse/expand works', async ({ page }) => {
    await page.goto('/problems/modus-ponens');

    // On mobile, the collapse button is inside the lg:hidden container
    const mobileLayout = page.locator('.lg\\:hidden');
    const collapseButton = mobileLayout.getByLabel('Collapse goals panel');
    await expect(collapseButton).toBeVisible();

    // Click to collapse
    await collapseButton.click();

    // Expand button should now appear
    const expandButton = mobileLayout.getByLabel('Expand goals panel');
    await expect(expandButton).toBeVisible();

    // Click to expand again
    await expandButton.click();
    await expect(mobileLayout.getByLabel('Collapse goals panel')).toBeVisible();
  });
});
