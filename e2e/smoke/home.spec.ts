import { test, expect } from '@playwright/test';

test.describe('Home page', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/');
  });

  test('loads with "Master Coq Proofs" heading', async ({ page }) => {
    await expect(page.getByRole('heading', { name: /Master Coq Proofs/i })).toBeVisible();
  });

  test('"Start Tutorial" and "Browse Problems" CTA buttons visible', async ({ page }) => {
    await expect(page.getByRole('link', { name: /Start Tutorial/i })).toBeVisible();
    await expect(page.getByRole('link', { name: /Browse Problems/i })).toBeVisible();
  });

  test('6 category cards visible', async ({ page }) => {
    const categories = ['Logic', 'Induction', 'Lists', 'Arithmetic', 'Data Structures', 'Relations'];
    for (const cat of categories) {
      await expect(page.getByRole('heading', { name: cat, exact: true })).toBeVisible();
    }
  });
});
