// Suppress Zustand persist middleware warnings in node test environment
// (no localStorage available — persist gracefully degrades but logs warnings)
for (const method of ['error', 'warn'] as const) {
  const original = console[method];
  console[method] = (...args: unknown[]) => {
    const msg = String(args[0] ?? '');
    if (msg.includes('[zustand persist middleware]')) return;
    original.apply(console, args);
  };
}
