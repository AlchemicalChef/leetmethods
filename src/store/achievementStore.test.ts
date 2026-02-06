import { describe, it, expect, beforeEach, vi } from 'vitest';
import { useAchievementStore } from './achievementStore';

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function resetStore() {
  useAchievementStore.setState({
    unlockedAchievements: {},
    pendingToasts: [],
  });
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

describe('achievementStore', () => {
  beforeEach(() => {
    resetStore();
  });

  // -- Initial state --------------------------------------------------------

  it('has correct initial state', () => {
    const state = useAchievementStore.getState();
    expect(state.unlockedAchievements).toEqual({});
    expect(state.pendingToasts).toEqual([]);
  });

  // -- unlock ---------------------------------------------------------------

  it('unlocks an achievement with a timestamp and queues a toast', () => {
    vi.useFakeTimers();
    vi.setSystemTime(new Date(2025, 5, 15, 12, 0, 0));
    const now = Date.now();

    useAchievementStore.getState().unlock('first-proof');

    const state = useAchievementStore.getState();
    expect(state.unlockedAchievements['first-proof']).toBe(now);
    expect(state.pendingToasts).toEqual(['first-proof']);

    vi.useRealTimers();
  });

  it('does not unlock the same achievement twice (deduplication)', () => {
    vi.useFakeTimers();
    vi.setSystemTime(new Date(2025, 5, 15, 12, 0, 0));
    const firstTimestamp = Date.now();

    useAchievementStore.getState().unlock('first-proof');

    // Advance time and try to unlock again
    vi.setSystemTime(new Date(2025, 5, 16, 12, 0, 0));
    useAchievementStore.getState().unlock('first-proof');

    const state = useAchievementStore.getState();
    // Timestamp should be the original, not updated
    expect(state.unlockedAchievements['first-proof']).toBe(firstTimestamp);
    // Should not add a duplicate toast
    expect(state.pendingToasts).toEqual(['first-proof']);

    vi.useRealTimers();
  });

  it('can unlock multiple different achievements', () => {
    useAchievementStore.getState().unlock('first-proof');
    useAchievementStore.getState().unlock('five-proofs');
    useAchievementStore.getState().unlock('no-hints');

    const state = useAchievementStore.getState();
    expect(Object.keys(state.unlockedAchievements)).toHaveLength(3);
    expect(state.pendingToasts).toEqual(['first-proof', 'five-proofs', 'no-hints']);
  });

  // -- clearToast -----------------------------------------------------------

  it('removes a specific toast from pendingToasts', () => {
    useAchievementStore.getState().unlock('first-proof');
    useAchievementStore.getState().unlock('five-proofs');

    useAchievementStore.getState().clearToast('first-proof');

    expect(useAchievementStore.getState().pendingToasts).toEqual(['five-proofs']);
  });

  it('does not affect other toasts when clearing one', () => {
    useAchievementStore.getState().unlock('a');
    useAchievementStore.getState().unlock('b');
    useAchievementStore.getState().unlock('c');

    useAchievementStore.getState().clearToast('b');

    expect(useAchievementStore.getState().pendingToasts).toEqual(['a', 'c']);
  });

  it('is a no-op when clearing a non-existent toast', () => {
    useAchievementStore.getState().unlock('first-proof');
    useAchievementStore.getState().clearToast('non-existent');
    expect(useAchievementStore.getState().pendingToasts).toEqual(['first-proof']);
  });

  it('clearing a toast does not remove the achievement itself', () => {
    useAchievementStore.getState().unlock('first-proof');
    useAchievementStore.getState().clearToast('first-proof');

    expect(useAchievementStore.getState().pendingToasts).toEqual([]);
    expect(useAchievementStore.getState().isUnlocked('first-proof')).toBe(true);
  });

  // -- isUnlocked -----------------------------------------------------------

  it('returns true for an unlocked achievement', () => {
    useAchievementStore.getState().unlock('first-proof');
    expect(useAchievementStore.getState().isUnlocked('first-proof')).toBe(true);
  });

  it('returns false for an achievement that has not been unlocked', () => {
    expect(useAchievementStore.getState().isUnlocked('first-proof')).toBe(false);
  });

  // -- getUnlockedIds -------------------------------------------------------

  it('returns an empty Set when nothing is unlocked', () => {
    const ids = useAchievementStore.getState().getUnlockedIds();
    expect(ids).toBeInstanceOf(Set);
    expect(ids.size).toBe(0);
  });

  it('returns a Set of all unlocked achievement IDs', () => {
    useAchievementStore.getState().unlock('first-proof');
    useAchievementStore.getState().unlock('streak-3');

    const ids = useAchievementStore.getState().getUnlockedIds();
    expect(ids.size).toBe(2);
    expect(ids.has('first-proof')).toBe(true);
    expect(ids.has('streak-3')).toBe(true);
    expect(ids.has('five-proofs')).toBe(false);
  });
});
