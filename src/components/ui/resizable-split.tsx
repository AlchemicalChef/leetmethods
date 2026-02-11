/**
 * @module ResizableSplit
 *
 * A generic two-panel resizable split view component that supports both
 * horizontal (side-by-side) and vertical (stacked) orientations.
 *
 * Users can drag the divider between the two panels to resize them.
 * The split ratio is constrained between configurable min/max bounds
 * to prevent either panel from becoming too small to be useful.
 *
 * This component is used in the problem solver and potentially other
 * layouts where a resizable split between an editor and a goals/output
 * panel is needed.
 *
 * Implementation details:
 *   - **Pointer events** are used instead of mouse events for better
 *     cross-device compatibility (touch screens, styluses, etc.).
 *   - **Pointer capture** (`setPointerCapture`) is used on the divider
 *     element to ensure drag events are received even when the pointer
 *     moves outside the divider's bounds. This prevents the drag from
 *     "sticking" if the user moves the cursor too fast.
 *   - **Ref-based drag tracking** (`draggingRef`) avoids re-renders during
 *     the drag operation. Only the final ratio change triggers a state update.
 *   - The divider has visual affordances: it changes color on hover and
 *     slightly expands (1px -> 1.5px) to indicate interactivity.
 *   - The children tuple type `[ReactNode, ReactNode]` enforces that
 *     exactly two children are provided at the type level.
 */
'use client';

import { useState, useCallback, useRef } from 'react';

/**
 * Props for the ResizableSplit component.
 *
 * @property direction - Split orientation: 'horizontal' places panels
 *   side-by-side, 'vertical' stacks them top-to-bottom. Defaults to 'horizontal'.
 * @property defaultRatio - Initial split ratio (0-1) where the value represents
 *   the fraction of space allocated to the first panel. Defaults to 0.5 (50/50).
 * @property minRatio - Minimum allowed ratio for the first panel. Prevents it
 *   from being collapsed too small. Defaults to 0.25 (25%).
 * @property maxRatio - Maximum allowed ratio for the first panel. Prevents it
 *   from pushing the second panel too small. Defaults to 0.75 (75%).
 * @property children - Exactly two React nodes: [firstPanel, secondPanel].
 * @property className - Optional additional CSS classes for the container.
 */
interface ResizableSplitProps {
  direction?: 'horizontal' | 'vertical';
  defaultRatio?: number;
  minRatio?: number;
  maxRatio?: number;
  children: [React.ReactNode, React.ReactNode];
  className?: string;
}

/**
 * Renders a resizable two-panel split view with a draggable divider.
 *
 * @param props - Configuration for the split view including direction,
 *   ratio bounds, and the two child panels.
 * @returns A flex container with two panels separated by a draggable divider.
 */
export function ResizableSplit({
  direction = 'horizontal',
  defaultRatio = 0.5,
  minRatio = 0.25,
  maxRatio = 0.75,
  children,
  className = '',
}: ResizableSplitProps) {
  /** Current split ratio (fraction of space for the first panel) */
  const [ratio, setRatio] = useState(defaultRatio);

  /** Ref to the outer container, used for coordinate calculations during drag */
  const containerRef = useRef<HTMLDivElement>(null);

  /**
   * Ref-based drag state flag.
   * Using a ref instead of state avoids re-renders on every pointer move
   * event during dragging, which would be wasteful since only the ratio
   * state update needs to trigger a re-render.
   */
  const draggingRef = useRef(false);

  /**
   * Handles the start of a drag operation on the divider.
   * Sets the dragging flag and captures the pointer to ensure continued
   * event delivery even if the pointer moves off the divider element.
   *
   * @param e - The pointer down event from the divider element.
   */
  const handlePointerDown = useCallback(
    (e: React.PointerEvent) => {
      e.preventDefault();
      draggingRef.current = true;
      (e.target as HTMLElement).setPointerCapture(e.pointerId);
    },
    []
  );

  /**
   * Handles pointer movement during a drag operation.
   * Calculates the new ratio based on the pointer's position relative
   * to the container's bounding rectangle, then clamps it to the
   * allowed [minRatio, maxRatio] range.
   *
   * @param e - The pointer move event from the divider element.
   */
  const handlePointerMove = useCallback(
    (e: React.PointerEvent) => {
      if (!draggingRef.current || !containerRef.current) return;

      const rect = containerRef.current.getBoundingClientRect();
      let newRatio: number;

      /* Calculate ratio based on pointer position within the container.
         For horizontal splits, use X coordinate relative to container width.
         For vertical splits, use Y coordinate relative to container height. */
      if (direction === 'horizontal') {
        newRatio = (e.clientX - rect.left) / rect.width;
      } else {
        newRatio = (e.clientY - rect.top) / rect.height;
      }

      /* Clamp the ratio to the allowed bounds */
      setRatio(Math.min(maxRatio, Math.max(minRatio, newRatio)));
    },
    [direction, minRatio, maxRatio]
  );

  /**
   * Handles the end of a drag operation.
   * Simply clears the dragging flag; pointer capture is automatically
   * released when the pointer is lifted.
   */
  const handlePointerUp = useCallback(() => {
    draggingRef.current = false;
  }, []);

  /** Whether the split is horizontal (side-by-side panels) */
  const isHorizontal = direction === 'horizontal';

  /** CSS size values for each panel, derived from the current ratio */
  const firstSize = `${ratio * 100}%`;
  const secondSize = `${(1 - ratio) * 100}%`;

  return (
    <div
      ref={containerRef}
      className={`flex ${isHorizontal ? 'flex-row' : 'flex-col'} ${className}`}
      style={{ height: '100%' }}
    >
      {/* First panel -- size controlled by the ratio, flex-shrink disabled
          to prevent it from being compressed by the second panel */}
      <div
        className="overflow-hidden"
        style={{ [isHorizontal ? 'width' : 'height']: firstSize, flexShrink: 0 }}
      >
        {children[0]}
      </div>

      {/* Draggable divider -- thin bar between the two panels.
          Changes cursor and slightly expands on hover to indicate interactivity.
          Pointer events drive the drag-to-resize behavior. */}
      <div
        onPointerDown={handlePointerDown}
        onPointerMove={handlePointerMove}
        onPointerUp={handlePointerUp}
        className={`
          flex-shrink-0 bg-border hover:bg-primary/30 transition-colors
          ${isHorizontal
            ? 'w-1 cursor-col-resize hover:w-1.5'
            : 'h-1 cursor-row-resize hover:h-1.5'
          }
        `}
      />

      {/* Second panel -- takes remaining space via flex-1.
          The explicit size style ensures accurate sizing during resize. */}
      <div
        className="overflow-hidden flex-1"
        style={{ [isHorizontal ? 'width' : 'height']: secondSize }}
      >
        {children[1]}
      </div>
    </div>
  );
}
