/**
 * Safe localStorage wrapper for Zustand persist middleware.
 *
 * In a client-side-only application that relies heavily on localStorage for all
 * state persistence (progress, achievements, editor content, custom problems),
 * hitting the browser's storage quota is a real risk -- especially on mobile
 * browsers with limited quotas (often 5MB).
 *
 * This module wraps the native `localStorage` API so that `setItem` calls
 * gracefully degrade instead of throwing. When a `QuotaExceededError` occurs,
 * the write is silently dropped and a warning is logged. The application
 * continues running with stale persisted state rather than crashing entirely.
 *
 * All other operations (`getItem`, `removeItem`, `clear`, `length`, `key`)
 * delegate directly to the native `localStorage` without modification.
 *
 * Usage: Pass `safeStorage` as the `storage` option to Zustand's `persist()`
 * middleware in any store that writes to localStorage.
 *
 * @module safe-storage
 */

import { createJSONStorage } from 'zustand/middleware';

/**
 * Creates a `Storage`-compatible object that wraps `localStorage` with
 * quota error protection on writes.
 *
 * @returns A `Storage` implementation where `setItem` catches `QuotaExceededError`
 *          and logs a warning instead of throwing.
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
        /**
         * Only swallow QuotaExceededError. Any other error (e.g., SecurityError
         * from iframe sandbox restrictions) is re-thrown so it surfaces as a
         * genuine bug rather than being silently ignored.
         */
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

/**
 * Pre-configured Zustand JSON storage adapter backed by the safe localStorage wrapper.
 *
 * Zustand's `createJSONStorage` handles JSON serialization/deserialization automatically.
 * The factory function is called lazily (only when storage is actually accessed), which
 * avoids errors during SSR where `localStorage` is not defined -- though in this
 * client-side-only app, SSR storage access should not occur.
 */
export const safeStorage = createJSONStorage(() => safePersistStorage());
