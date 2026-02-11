/**
 * @module Dialog
 *
 * A custom modal dialog component built with React portals.
 *
 * This component renders a centered modal overlay with:
 *   - A semi-transparent backdrop that closes the dialog on click
 *   - Escape key support for keyboard dismissal
 *   - An optional title bar with a close button
 *   - Scrollable content area for long content
 *
 * This is a custom implementation rather than using Radix UI's Dialog
 * because the app needs a lightweight, portal-based dialog that integrates
 * cleanly with the existing UI without the full Radix Dialog dependency.
 *
 * Implementation details:
 *   - **React Portal**: The dialog is rendered via `createPortal` into
 *     `document.body` to escape any parent overflow/z-index stacking
 *     contexts. This ensures the dialog always appears above all other
 *     content regardless of where the component is used in the tree.
 *   - **Escape key handling**: A global `keydown` listener is added when
 *     the dialog opens and cleaned up when it closes. The listener is
 *     memoized with `useCallback` to maintain stable identity for the
 *     event listener add/remove cycle.
 *   - **Backdrop click**: The backdrop div has an `onClick` handler that
 *     calls `onClose`. The inner dialog content has `relative z-10` to
 *     sit above the backdrop and prevent clicks on the content from
 *     bubbling to the backdrop.
 *   - **z-index**: Uses z-[100] to sit above the navbar (z-50) but below
 *     achievement toasts (z-[200]).
 *   - **Max height**: Content area is limited to 85vh with overflow-y-auto
 *     to handle long content without breaking the viewport layout.
 */
'use client';

import { useEffect, useCallback } from 'react';
import { createPortal } from 'react-dom';
import { X } from 'lucide-react';

/**
 * Props for the Dialog component.
 *
 * @property open - Whether the dialog is currently visible. When false,
 *   the component renders nothing.
 * @property onClose - Callback invoked when the user dismisses the dialog
 *   (via backdrop click, Escape key, or the close button).
 * @property title - Optional title displayed in a header bar at the top
 *   of the dialog. When provided, a close button is also shown.
 * @property children - The dialog body content.
 */
interface DialogProps {
  open: boolean;
  onClose: () => void;
  title?: string;
  children: React.ReactNode;
}

/**
 * Renders a modal dialog as a React portal with backdrop, keyboard
 * dismissal, and optional title bar.
 *
 * @param props - Dialog configuration and content.
 * @returns A portal-rendered modal dialog, or null when `open` is false.
 */
export function Dialog({ open, onClose, title, children }: DialogProps) {
  /**
   * Memoized keydown handler for Escape key dismissal.
   * Wrapped in useCallback so the event listener can be properly
   * cleaned up when the effect re-runs or the component unmounts.
   */
  const handleKeyDown = useCallback(
    (e: KeyboardEvent) => {
      if (e.key === 'Escape') onClose();
    },
    [onClose]
  );

  /**
   * Attach/detach the global keydown listener based on the dialog's
   * open state. The listener is only active while the dialog is visible
   * to avoid intercepting Escape key presses when no dialog is shown.
   */
  useEffect(() => {
    if (open) {
      document.addEventListener('keydown', handleKeyDown);
      return () => document.removeEventListener('keydown', handleKeyDown);
    }
  }, [open, handleKeyDown]);

  /* Don't render anything when the dialog is closed */
  if (!open) return null;

  return createPortal(
    <div className="fixed inset-0 z-[100] flex items-center justify-center">
      {/* Semi-transparent backdrop -- clicking it dismisses the dialog */}
      <div className="fixed inset-0 bg-black/50" onClick={onClose} />

      {/* Dialog content container.
          z-10 ensures it sits above the backdrop so content clicks don't
          trigger the backdrop's onClose handler.
          max-h-[85vh] with overflow-y-auto handles long content gracefully. */}
      <div className="relative z-10 bg-background border rounded-lg shadow-lg max-w-lg w-full mx-4 max-h-[85vh] overflow-y-auto">
        {/* Optional title bar with close button */}
        {title && (
          <div className="flex items-center justify-between px-6 py-4 border-b">
            <h2 className="text-lg font-semibold">{title}</h2>
            <button
              onClick={onClose}
              className="text-muted-foreground hover:text-foreground transition-colors"
            >
              <X className="h-4 w-4" />
            </button>
          </div>
        )}

        {/* Dialog body content area */}
        <div className="px-6 py-4">{children}</div>
      </div>
    </div>,
    document.body
  );
}
