'use client';

import { useState, useCallback, useRef } from 'react';

interface ResizableSplitProps {
  direction?: 'horizontal' | 'vertical';
  defaultRatio?: number;
  minRatio?: number;
  maxRatio?: number;
  children: [React.ReactNode, React.ReactNode];
  className?: string;
}

export function ResizableSplit({
  direction = 'horizontal',
  defaultRatio = 0.5,
  minRatio = 0.25,
  maxRatio = 0.75,
  children,
  className = '',
}: ResizableSplitProps) {
  const [ratio, setRatio] = useState(defaultRatio);
  const containerRef = useRef<HTMLDivElement>(null);
  const draggingRef = useRef(false);

  const handlePointerDown = useCallback(
    (e: React.PointerEvent) => {
      e.preventDefault();
      draggingRef.current = true;
      (e.target as HTMLElement).setPointerCapture(e.pointerId);
    },
    []
  );

  const handlePointerMove = useCallback(
    (e: React.PointerEvent) => {
      if (!draggingRef.current || !containerRef.current) return;

      const rect = containerRef.current.getBoundingClientRect();
      let newRatio: number;

      if (direction === 'horizontal') {
        newRatio = (e.clientX - rect.left) / rect.width;
      } else {
        newRatio = (e.clientY - rect.top) / rect.height;
      }

      setRatio(Math.min(maxRatio, Math.max(minRatio, newRatio)));
    },
    [direction, minRatio, maxRatio]
  );

  const handlePointerUp = useCallback(() => {
    draggingRef.current = false;
  }, []);

  const isHorizontal = direction === 'horizontal';
  const firstSize = `${ratio * 100}%`;
  const secondSize = `${(1 - ratio) * 100}%`;

  return (
    <div
      ref={containerRef}
      className={`flex ${isHorizontal ? 'flex-row' : 'flex-col'} ${className}`}
      style={{ height: '100%' }}
    >
      <div
        className="overflow-hidden"
        style={{ [isHorizontal ? 'width' : 'height']: firstSize, flexShrink: 0 }}
      >
        {children[0]}
      </div>

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

      <div
        className="overflow-hidden flex-1"
        style={{ [isHorizontal ? 'width' : 'height']: secondSize }}
      >
        {children[1]}
      </div>
    </div>
  );
}
