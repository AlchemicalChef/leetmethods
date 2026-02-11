import { test, expect } from '@playwright/test';

test.describe('Keyboard shortcuts dialog', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/problems/modus-ponens');
  });

  test('dialog opens when clicking shortcuts button', async ({ page }) => {
    // Click the keyboard shortcuts button in the toolbar
    await page.getByLabel('Keyboard shortcuts').first().click();

    // Dialog with title should appear
    await expect(page.getByRole('heading', { name: 'Keyboard Shortcuts' })).toBeVisible();
  });

  test('dialog shows Execution, Editor, General sections', async ({ page }) => {
    await page.getByLabel('Keyboard shortcuts').first().click();

    // Section headings
    await expect(page.getByText('Execution')).toBeVisible();
    await expect(page.getByText('Editor')).toBeVisible();
    await expect(page.getByText('General')).toBeVisible();

    // Sample shortcut descriptions
    await expect(page.getByText('Execute next statement')).toBeVisible();
    await expect(page.getByText('Undo edit')).toBeVisible();
  });

  test('dialog closes when clicking X', async ({ page }) => {
    await page.getByLabel('Keyboard shortcuts').first().click();
    await expect(page.getByRole('heading', { name: 'Keyboard Shortcuts' })).toBeVisible();

    // Click the close button (X icon in the dialog header)
    // The dialog's close button is in the header area next to the title
    const closeButton = page.locator('.fixed').locator('button').filter({ has: page.locator('svg.lucide-x') });
    await closeButton.click();

    // Dialog should be gone
    await expect(page.getByRole('heading', { name: 'Keyboard Shortcuts' })).not.toBeVisible();
  });
});
