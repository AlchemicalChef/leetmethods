import { describe, it, expect } from 'vitest';
import { formatError } from './format-error';

describe('formatError', () => {
  it('returns error message for Error instance', () => {
    expect(formatError(new Error('Something went wrong'), 'fallback')).toBe('Something went wrong');
  });

  it('returns string for string error', () => {
    expect(formatError('Error message', 'fallback')).toBe('Error message');
  });

  it('returns fallback for number', () => {
    expect(formatError(42, 'fallback')).toBe('fallback');
  });

  it('returns fallback for null', () => {
    expect(formatError(null, 'fallback')).toBe('fallback');
  });

  it('returns fallback for undefined', () => {
    expect(formatError(undefined, 'fallback')).toBe('fallback');
  });

  it('returns fallback for plain object', () => {
    expect(formatError({ message: 'error' }, 'fallback')).toBe('fallback');
  });

  it('returns message for TypeError', () => {
    expect(formatError(new TypeError('Type error'), 'fallback')).toBe('Type error');
  });

  it('returns message for RangeError', () => {
    expect(formatError(new RangeError('Out of range'), 'fallback')).toBe('Out of range');
  });

  it('returns empty string for empty string error (not fallback)', () => {
    expect(formatError('', 'fallback')).toBe('');
  });

  it('returns fallback for boolean', () => {
    expect(formatError(false, 'fallback')).toBe('fallback');
  });

  it('returns fallback for array', () => {
    expect(formatError(['error'], 'fallback')).toBe('fallback');
  });
});
