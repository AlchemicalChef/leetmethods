// Provide a working localStorage for Zustand persist middleware in node tests.
// Node 22+ has a built-in localStorage stub that lacks functional methods,
// so we always override with a complete in-memory implementation.
const store: Record<string, string> = {};
globalThis.localStorage = {
  getItem: (key: string) => store[key] ?? null,
  setItem: (key: string, value: string) => { store[key] = value; },
  removeItem: (key: string) => { delete store[key]; },
  clear: () => { for (const k of Object.keys(store)) delete store[k]; },
  get length() { return Object.keys(store).length; },
  key: (index: number) => Object.keys(store)[index] ?? null,
} as Storage;

// Suppress Zustand persist middleware warnings in node test environment
for (const method of ['error', 'warn'] as const) {
  const original = console[method];
  console[method] = (...args: unknown[]) => {
    const msg = String(args[0] ?? '');
    if (msg.includes('[zustand persist middleware]')) return;
    original.apply(console, args);
  };
}
