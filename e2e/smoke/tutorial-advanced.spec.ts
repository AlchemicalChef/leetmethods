import { test, expect } from '@playwright/test';

test.describe('Tutorial advanced flows', () => {
  test('last step shows completion link', async ({ page }) => {
    await page.goto('/tutorial/basics');
    await page.getByText(/Step 1:/).waitFor({ state: 'visible' });

    // Jump to last step (step 5) via dot indicator
    const dot5 = page.locator('button.rounded-full').filter({ hasText: '5' });
    await dot5.click();
    await expect(page.getByText(/Step 5:/)).toBeVisible();

    // Instead of "Next Step", should show completion link
    await expect(page.getByRole('link', { name: /Continue to Applied Methods/ })).toBeVisible();
    await expect(page.getByRole('link', { name: /Continue to Applied Methods/ })).toHaveAttribute(
      'href',
      '/tutorial/applied-methods'
    );
  });

  test('applied-methods tutorial loads', async ({ page }) => {
    await page.goto('/tutorial/applied-methods');
    await page.getByText(/Step 1:/).waitFor({ state: 'visible' });

    await expect(page.getByRole('heading', { name: /Tutorial: Applied Methods/ })).toBeVisible();
  });

  test('Show Hint button reveals hint text', async ({ page }) => {
    await page.goto('/tutorial/basics');
    await page.getByText(/Step 1:/).waitFor({ state: 'visible' });

    // Click "Show Hint"
    await page.getByRole('button', { name: 'Show Hint' }).click();

    // Hint should appear in a yellow-bordered box
    const hintBox = page.locator('.border-yellow-200, .border-yellow-900');
    await expect(hintBox.first()).toBeVisible();
    await expect(page.getByText('Hint:')).toBeVisible();
  });

  test('step indicator dots have correct styling for visited steps', async ({ page }) => {
    await page.goto('/tutorial/basics');
    await page.getByText(/Step 1:/).waitFor({ state: 'visible' });

    // Navigate to step 3 by clicking dot 3
    const dot3 = page.locator('button.rounded-full').filter({ hasText: '3' });
    await dot3.click();
    await expect(page.getByText(/Step 3:/)).toBeVisible();

    // Dots 1 and 2 should have green styling (visited/completed)
    const dot1 = page.locator('button.rounded-full').filter({ hasText: '1' });
    const dot2 = page.locator('button.rounded-full').filter({ hasText: '2' });

    await expect(dot1).toHaveClass(/bg-green-100/);
    await expect(dot2).toHaveClass(/bg-green-100/);

    // Dot 3 (current) should have primary styling
    await expect(dot3).toHaveClass(/bg-primary/);
  });
});
