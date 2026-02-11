import { test, expect } from '@playwright/test';
import { waitForCoqReady } from '../fixtures/test-fixtures';

test.describe('Problem solver page', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/problems/modus-ponens');
  });

  test('loads with description, editor, toolbar, and goals panel', async ({ page }) => {
    // Problem title
    await expect(page.getByRole('heading', { name: /Modus Ponens/i })).toBeVisible();

    // CodeMirror editor (desktop + mobile layout can produce 2; use first)
    await expect(page.locator('.cm-editor').first()).toBeVisible();

    // Toolbar buttons (aria-labels) — use first() since desktop/mobile both render
    await expect(page.getByLabel('Execute all').first()).toBeVisible();
    await expect(page.getByLabel('Submit proof').first()).toBeVisible();
    await expect(page.getByLabel('Reset').first()).toBeVisible();

    // Goals panel header
    await expect(page.getByText('Goals').first()).toBeVisible();
  });

  test('Coq runtime initializes to Ready', async ({ page }) => {
    await waitForCoqReady(page);
    await expect(page.getByText('Ready', { exact: true }).first()).toBeVisible();
  });

  test('hint reveal works', async ({ page }) => {
    // ProblemDescription renders hint button as "Show Hint 1"
    const hintButton = page.getByRole('button', { name: /Show Hint 1/i });
    await expect(hintButton).toBeVisible();
    await hintButton.click();

    // Hint text should appear (Hint 1: ...) — desktop + mobile both render, use first()
    await expect(page.getByText(/Hint 1:/).first()).toBeVisible();
  });
});
