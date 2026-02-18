import { describe, it, expect } from 'vitest';
import { generateSlug } from './slug';

describe('generateSlug', () => {
  it('converts basic title to slug with custom prefix', () => {
    expect(generateSlug('My First Proof', [])).toBe('custom-my-first-proof');
  });

  it('returns custom-untitled for empty title', () => {
    expect(generateSlug('', [])).toBe('custom-untitled');
  });

  it('returns custom-untitled for whitespace-only title', () => {
    expect(generateSlug('   ', [])).toBe('custom-untitled');
  });

  it('replaces special characters with hyphens', () => {
    expect(generateSlug('Hello! World? #Test', [])).toBe('custom-hello-world-test');
  });

  it('strips leading hyphens', () => {
    expect(generateSlug('---hello', [])).toBe('custom-hello');
  });

  it('strips trailing hyphens', () => {
    expect(generateSlug('hello---', [])).toBe('custom-hello');
  });

  it('converts uppercase to lowercase', () => {
    expect(generateSlug('HELLO WORLD', [])).toBe('custom-hello-world');
  });

  it('truncates long title to 50 characters before prefix', () => {
    const longTitle = 'a'.repeat(60);
    const result = generateSlug(longTitle, []);
    expect(result).toBe('custom-' + 'a'.repeat(50));
  });

  it('returns base slug when no collision', () => {
    expect(generateSlug('Test', ['custom-other'])).toBe('custom-test');
  });

  it('appends -2 for first collision', () => {
    expect(generateSlug('Test', ['custom-test'])).toBe('custom-test-2');
  });

  it('increments suffix for multiple collisions', () => {
    expect(generateSlug('Test', ['custom-test', 'custom-test-2'])).toBe('custom-test-3');
  });

  it('handles collision with untitled', () => {
    expect(generateSlug('', ['custom-untitled'])).toBe('custom-untitled-2');
  });

  it('preserves numbers in title', () => {
    expect(generateSlug('Problem 123', [])).toBe('custom-problem-123');
  });

  it('strips unicode characters', () => {
    expect(generateSlug('Hello 世界', [])).toBe('custom-hello');
  });

  it('collapses multiple special characters into one hyphen', () => {
    expect(generateSlug('Hello!!!World', [])).toBe('custom-hello-world');
  });

  it('handles title with only special characters', () => {
    expect(generateSlug('!@#$%^&*()', [])).toBe('custom-untitled');
  });

  it('handles truncation with collision', () => {
    const longTitle = 'a'.repeat(60);
    const base = 'custom-' + 'a'.repeat(50);
    expect(generateSlug(longTitle, [base])).toBe(base + '-2');
  });
});
