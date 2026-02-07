import { useState, useEffect } from 'react';

/** Returns true after the first client render (hydration complete). */
export function useHydrated(): boolean {
  const [hydrated, setHydrated] = useState(false);
  useEffect(() => {
    setHydrated(true);
  }, []);
  return hydrated;
}
