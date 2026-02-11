import { test, expect } from '@playwright/test';

test.describe('Learn page', () => {
  test.beforeEach(async ({ page }) => {
    await page.goto('/learn');
  });

  test('loads with heading, progress overview, learning paths, and tabs', async ({ page }) => {
    await expect(page.getByRole('heading', { name: 'Learn Coq' })).toBeVisible();

    // ProgressOverview section
    await expect(page.getByText(/Your Progress/i)).toBeVisible();

    // Learning Paths heading
    await expect(page.getByRole('heading', { name: 'Learning Paths' })).toBeVisible();

    // Tab navigation
    await expect(page.getByRole('tab', { name: 'Concepts' })).toBeVisible();
    await expect(page.getByRole('tab', { name: 'Tactic Reference' })).toBeVisible();
    await expect(page.getByRole('tab', { name: 'Playground' })).toBeVisible();
  });

  test('learning path cards are visible with title, difficulty badge, and progress', async ({ page }) => {
    // At least one path card link
    const pathCards = page.locator('a[href^="/learn/"]');
    await expect(pathCards.first()).toBeVisible();

    // First card has a title (h3)
    const firstCard = pathCards.first();
    await expect(firstCard.locator('h3')).toBeVisible();

    // Difficulty badge inside the card
    await expect(firstCard.locator('.inline-flex, [class*="badge"]').first()).toBeVisible();

    // Progress fraction like "0/X"
    await expect(firstCard.getByText(/\d+\/\d+/)).toBeVisible();
  });

  test('tab switching shows different content', async ({ page }) => {
    // Click Tactic Reference tab
    await page.getByRole('tab', { name: 'Tactic Reference' }).click();
    // Tactic reference content should appear — look for the "intros" button specifically
    await expect(page.getByRole('button', { name: /intros/i }).first()).toBeVisible();

    // Click Playground tab
    await page.getByRole('tab', { name: 'Playground' }).click();
    // Playground content should appear — look for the editor or playground-specific content
    await expect(page.locator('[role="tabpanel"]').last()).toBeVisible();
  });

  test('path detail page loads with title, back link, progress bar, and step list', async ({ page }) => {
    await page.goto('/learn/boolean-basics');

    // Title
    await expect(page.getByRole('heading', { level: 1 })).toBeVisible();

    // Back to Learn link
    await expect(page.getByText('Back to Learn')).toBeVisible();

    // Progress bar (the "X/Y complete" text)
    await expect(page.getByText(/\d+\/\d+ complete/)).toBeVisible();
  });
});
