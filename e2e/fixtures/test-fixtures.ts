import { test as base, type Page } from '@playwright/test';
import { progressSeed, editorSeed, tutorialProgressValue } from './storage-seeds';

/**
 * Custom Playwright test with fixtures for seeded localStorage.
 */
export const test = base.extend<{ seededPage: Page }>({
  seededPage: async ({ page }, use) => {
    // Navigate first so we can set localStorage on the correct origin
    await page.goto('/');
    await page.waitForLoadState('domcontentloaded');

    // Inject Zustand-persisted data
    await page.evaluate(
      ({ progress, editor, tutorialStep }) => {
        localStorage.setItem('leetmethods-progress', progress);
        localStorage.setItem('leetmethods-editor', editor);
        localStorage.setItem('leetmethods-tutorial-progress', tutorialStep);
      },
      {
        progress: progressSeed(),
        editor: editorSeed(),
        tutorialStep: tutorialProgressValue,
      }
    );

    await use(page);
  },
});

export { expect } from '@playwright/test';

/**
 * Wait for the Coq runtime to finish initializing.
 * Looks for the "Ready" status indicator in EditorToolbar.
 */
export async function waitForCoqReady(page: Page, timeout = 45_000) {
  // Wait for the loading bar to disappear (if it appeared)
  const loadingBar = page.getByText('Initializing Coq runtime...').first();
  if (await loadingBar.isVisible({ timeout: 5_000 }).catch(() => false)) {
    await loadingBar.waitFor({ state: 'hidden', timeout });
  }

  // Wait for the green "Ready" status indicator (use first() since desktop/mobile both render)
  await page.getByText('Ready', { exact: true }).first().waitFor({ state: 'visible', timeout });
}
