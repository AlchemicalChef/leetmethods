import { test, expect } from '@playwright/test';

test.describe('Theme toggle', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
  });

  test('toggle dropdown shows Light, Dark, System options', async ({ page }) => {
    // Click the theme toggle button (the first visible one — desktop or mobile)
    await page.getByRole('button', { name: 'Toggle theme' }).first().click();

    // Dropdown menu items
    await expect(page.getByRole('menuitem').filter({ hasText: 'Light' })).toBeVisible();
    await expect(page.getByRole('menuitem').filter({ hasText: 'Dark' })).toBeVisible();
    await expect(page.getByRole('menuitem').filter({ hasText: 'System' })).toBeVisible();
  });

  test('switch to dark mode', async ({ page }) => {
    await page.getByRole('button', { name: 'Toggle theme' }).first().click();
    await page.getByRole('menuitem').filter({ hasText: 'Dark' }).click();

    // next-themes applies class asynchronously — use polling
    await expect(page.locator('html')).toHaveClass(/dark/);

    // Preference survives reload
    await page.reload();
    await expect(page.locator('html')).toHaveClass(/dark/);
  });

  test('switch back to light mode', async ({ page }) => {
    // First go dark
    await page.getByRole('button', { name: 'Toggle theme' }).first().click();
    await page.getByRole('menuitem').filter({ hasText: 'Dark' }).click();
    await expect(page.locator('html')).toHaveClass(/dark/);

    // Now go light
    await page.getByRole('button', { name: 'Toggle theme' }).first().click();
    await page.getByRole('menuitem').filter({ hasText: 'Light' }).click();

    // dark class should be removed
    await expect(page.locator('html')).not.toHaveClass(/dark/);
  });
});
