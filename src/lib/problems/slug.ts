export function generateSlug(title: string, existingSlugs: string[]): string {
  const base = 'custom-' + title
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, '-')
    .replace(/(^-|-$)/g, '')
    .slice(0, 50);

  if (!existingSlugs.includes(base)) return base;

  let suffix = 2;
  while (existingSlugs.includes(`${base}-${suffix}`)) {
    suffix++;
  }
  return `${base}-${suffix}`;
}
