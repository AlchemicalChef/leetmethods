import { test as baseTest, expect as baseExpect } from '@playwright/test';
import { test, expect } from '../fixtures/test-fixtures';

baseTest.describe('Stats page (no seed)', () => {
  baseTest('loads with stat cards', async ({ page }) => {
    await page.goto('/stats');

    // Stat card labels — use exact match to avoid matching achievement descriptions
    await baseExpect(page.getByText('Solved', { exact: true })).toBeVisible();
    await baseExpect(page.getByText('Complete', { exact: true })).toBeVisible();
    await baseExpect(page.getByText('Streak', { exact: true })).toBeVisible();
    await baseExpect(page.getByText('Avg. Time', { exact: true })).toBeVisible();
  });
});

test.describe('Stats page (seeded)', () => {
  test('seeded progress shows non-zero values', async ({ seededPage: page }) => {
    await page.goto('/stats');

    // With 3 completed problems, the "Solved" stat card value should show "3/XX"
    // The stat card renders: <span>Solved</span> then <div class="text-2xl font-bold">3/44</div>
    // Use the card container to scope the query
    const solvedValue = page.locator('[class*="text-2xl"]').filter({ hasText: /^3\// });
    await expect(solvedValue).toBeVisible();

    // Streak should show non-zero (1 day)
    const streakValue = page.locator('[class*="text-2xl"]').filter({ hasText: /1 day/ });
    await expect(streakValue).toBeVisible();
  });
});
