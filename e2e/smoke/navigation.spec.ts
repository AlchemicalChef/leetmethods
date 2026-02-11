import { test, expect } from '@playwright/test';

test.describe('Navigation', () => {
  test('navbar links navigate correctly', async ({ page }) => {
    await page.goto('/');

    // Desktop nav — Learn link
    await page.getByRole('link', { name: /Learn/i }).click();
    await expect(page).toHaveURL('/learn');

    // Stats link
    await page.getByRole('link', { name: /Stats/i }).click();
    await expect(page).toHaveURL('/stats');
  });

  test('/tutorial shows tutorial listing page', async ({ page }) => {
    await page.goto('/tutorial');
    await expect(page).toHaveURL('/tutorial');
    await expect(page.getByRole('heading', { name: 'Tutorials' })).toBeVisible();
    await expect(page.getByRole('link', { name: /Basics/ })).toBeVisible();
  });

  test('home CTA "Try Your First Problem" links to /problems/modus-ponens', async ({ page }) => {
    await page.goto('/');
    const cta = page.getByRole('link', { name: /Try Your First Problem/i });
    await expect(cta).toBeVisible();
    await expect(cta).toHaveAttribute('href', '/problems/modus-ponens');
  });
});
