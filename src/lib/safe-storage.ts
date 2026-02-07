import { createJSONStorage } from 'zustand/middleware';

/**
 * A localStorage wrapper that catches QuotaExceededError on writes.
 * Reads and deletes work normally; setItem swallows quota errors
 * so the app continues running with stale persisted state rather than crashing.
 */
function safePersistStorage(): Storage {
  return {
    get length() { return localStorage.length; },
    key(index: number) { return localStorage.key(index); },
    getItem(name: string) {
      return localStorage.getItem(name);
    },
    setItem(name: string, value: string) {
      try {
        localStorage.setItem(name, value);
      } catch (e) {
        if (e instanceof DOMException && e.name === 'QuotaExceededError') {
          console.warn(`[storage] localStorage quota exceeded for key "${name}". State will not be persisted until space is freed.`);
        } else {
          throw e;
        }
      }
    },
    removeItem(name: string) {
      localStorage.removeItem(name);
    },
    clear() {
      localStorage.clear();
    },
  };
}

export const safeStorage = createJSONStorage(() => safePersistStorage());
