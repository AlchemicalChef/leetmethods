import { test, expect } from '@playwright/test';

test.describe('Custom problem creation', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/problems/custom/create');
  });

  test('create page loads with all form sections', async ({ page }) => {
    // Page heading
    await expect(page.getByRole('heading', { name: 'Create Custom Problem' })).toBeVisible();

    // Section headings
    await expect(page.getByText('Problem Metadata')).toBeVisible();
    await expect(page.getByText('Coq Code')).toBeVisible();
    await expect(page.getByText('Hints')).toBeVisible();
    await expect(page.getByText('Verify & Save')).toBeVisible();

    // Key form fields
    await expect(page.getByPlaceholder('e.g., Prove Modus Ponens')).toBeVisible();
    await expect(page.getByRole('button', { name: /Test Solution/ })).toBeVisible();
  });

  test('form validation errors appear on empty title', async ({ page }) => {
    // Clear the title field (already empty) and click Test Solution
    await page.getByRole('button', { name: /Test Solution/ }).click();

    // Title validation error
    await expect(page.getByText('Title must be at least 3 characters')).toBeVisible();
  });

  test('solution validation error when Qed. is missing', async ({ page }) => {
    // Fill in a valid title to pass that validation
    await page.getByPlaceholder('e.g., Prove Modus Ponens').fill('My Test Problem');

    // Clear the solution textarea — find it by its default content "Qed."
    const solutionTextarea = page.locator('textarea').filter({ hasText: 'Qed.' });
    await solutionTextarea.fill('Theorem my_theorem : True.\nProof.\n  exact I.');

    await page.getByRole('button', { name: /Test Solution/ }).click();

    await expect(page.getByText('Solution must contain Qed.')).toBeVisible();
  });

  test('add and remove hints', async ({ page }) => {
    // Initially there is 1 hint input
    const hintInputs = page.locator('input[placeholder="Enter a hint..."]');
    await expect(hintInputs).toHaveCount(1);

    // Click "Add Hint" to add a second
    await page.getByRole('button', { name: /Add Hint/ }).click();
    await expect(hintInputs).toHaveCount(2);

    // Remove the first hint by clicking the trash button
    const trashButtons = page.locator('button').filter({ has: page.locator('svg.lucide-trash-2') });
    await trashButtons.first().click();
    await expect(hintInputs).toHaveCount(1);
  });

  test('cancel button navigates back to problems page', async ({ page }) => {
    await page.getByRole('button', { name: 'Cancel' }).click();
    await expect(page).toHaveURL('/problems');
  });
});
