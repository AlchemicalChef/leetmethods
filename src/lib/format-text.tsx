/**
 * Safe markdown-like text formatting component for LeetMethods.
 *
 * Renders a subset of Markdown syntax as React elements without using
 * `dangerouslySetInnerHTML`. This is used throughout the application to
 * format problem descriptions, tutorial step content, and hint text.
 *
 * Supported syntax:
 * - **Bold**: `**text**`
 * - *Italic*: `*text*`
 * - `Inline code`: `` `code` ``
 * - Code blocks: ``` ```language ... ``` ```
 * - Headers: `#`, `##`, `###`
 * - Paragraph breaks: blank lines
 *
 * Design decisions:
 * - Security: All text is rendered via React elements (no innerHTML), preventing XSS.
 * - Simplicity: This is intentionally NOT a full Markdown parser. It covers only
 *   the formatting needed for problem/tutorial content, avoiding the weight of a
 *   library like `react-markdown`.
 * - Inline formatting uses a greedy left-to-right scan. Bold is matched before
 *   italic to correctly handle `**bold**` vs `*italic*`.
 *
 * @module format-text
 */

import React from 'react';

/**
 * Renders a text string with markdown-like formatting as React elements.
 *
 * The component processes the input line-by-line, handling block-level elements
 * (code blocks, headers, paragraphs) first, then applying inline formatting
 * (bold, italic, inline code) within text lines.
 *
 * @param props.text - The raw text string to format. May contain newlines and
 *                     markdown-like syntax.
 * @returns A React fragment containing the formatted elements.
 */
export function FormattedDescription({ text }: { text: string }) {
  const lines = text.split('\n');
  const elements: React.ReactNode[] = [];
  /** Accumulates inline content for the current paragraph being built. */
  let currentParagraph: React.ReactNode[] = [];
  /** Whether we are currently inside a fenced code block. */
  let inCodeBlock = false;
  /** Accumulates lines of code inside a fenced code block. */
  let codeBlockContent: string[] = [];
  /** The language identifier from the opening ``` fence (e.g., "coq"). */
  let codeBlockLang = '';
  /** Monotonically increasing key for top-level React elements. */
  let key = 0;

  /**
   * Flushes the accumulated `currentParagraph` content into a `<p>` element
   * and pushes it onto the `elements` array. Resets `currentParagraph` to empty.
   * No-ops if the paragraph buffer is empty.
   */
  const flushParagraph = () => {
    if (currentParagraph.length > 0) {
      elements.push(<p key={key++}>{currentParagraph}</p>);
      currentParagraph = [];
    }
  };

  /**
   * Counter for generating unique React keys for inline elements.
   * Separate from the top-level `key` to avoid collisions.
   */
  let inlineKeyCounter = 0;

  /**
   * Parses a single line of text and returns an array of React nodes with
   * inline formatting applied (bold, italic, inline code).
   *
   * The parser scans left-to-right through the `remaining` string, matching
   * patterns at the current position:
   * 1. `**...**` for bold (checked first to avoid false italic matches)
   * 2. `*...*` for italic
   * 3. `` `...` `` for inline code
   * 4. Plain text up to the next special character
   *
   * When a special character (`*` or `` ` ``) is encountered at position 0
   * but doesn't start a valid pattern, it is emitted as a literal character
   * to prevent infinite loops.
   *
   * @param line - A single line of text to process for inline formatting.
   * @returns An array of React nodes representing the formatted line.
   */
  const formatInlineText = (line: string): React.ReactNode[] => {
    const result: React.ReactNode[] = [];
    let remaining = line;

    while (remaining.length > 0) {
      /* -- Bold: **text** -- */
      const boldMatch = remaining.match(/^\*\*(.+?)\*\*/);
      if (boldMatch) {
        result.push(<strong key={`inline-${inlineKeyCounter++}`}>{boldMatch[1]}</strong>);
        remaining = remaining.slice(boldMatch[0].length);
        continue;
      }

      /* -- Italic: *text* -- */
      const italicMatch = remaining.match(/^\*(.+?)\*/);
      if (italicMatch) {
        result.push(<em key={`inline-${inlineKeyCounter++}`}>{italicMatch[1]}</em>);
        remaining = remaining.slice(italicMatch[0].length);
        continue;
      }

      /* -- Inline code: `text` -- */
      const codeMatch = remaining.match(/^`([^`]+)`/);
      if (codeMatch) {
        result.push(
          <code key={`inline-${inlineKeyCounter++}`} className="bg-muted px-1 py-0.5 rounded text-sm font-mono">
            {codeMatch[1]}
          </code>
        );
        remaining = remaining.slice(codeMatch[0].length);
        continue;
      }

      /**
       * Plain text segment: consume characters up to the next special character
       * (`*` or `` ` ``). If the current character IS a special character but
       * didn't match any pattern above, emit it as a single literal character
       * to avoid an infinite loop.
       */
      const nextSpecial = remaining.search(/\*|`/);
      if (nextSpecial === -1) {
        result.push(<span key={`inline-${inlineKeyCounter++}`}>{remaining}</span>);
        break;
      } else if (nextSpecial === 0) {
        result.push(<span key={`inline-${inlineKeyCounter++}`}>{remaining[0]}</span>);
        remaining = remaining.slice(1);
      } else {
        result.push(<span key={`inline-${inlineKeyCounter++}`}>{remaining.slice(0, nextSpecial)}</span>);
        remaining = remaining.slice(nextSpecial);
      }
    }

    return result;
  };

  /* ---- Main line-by-line processing loop ---- */
  for (const line of lines) {
    /* -- Fenced code block toggle: lines starting with ``` -- */
    if (line.startsWith('```')) {
      if (!inCodeBlock) {
        flushParagraph();
        inCodeBlock = true;
        codeBlockLang = line.slice(3).trim();
        codeBlockContent = [];
      } else {
        elements.push(
          <pre key={key++} className="bg-muted p-4 rounded-md overflow-x-auto">
            <code className={codeBlockLang ? `language-${codeBlockLang}` : ''}>
              {codeBlockContent.join('\n')}
            </code>
          </pre>
        );
        inCodeBlock = false;
        codeBlockContent = [];
        codeBlockLang = '';
      }
      continue;
    }

    /* -- Inside a code block: accumulate lines verbatim -- */
    if (inCodeBlock) {
      codeBlockContent.push(line);
      continue;
    }

    /* -- Headers: h3 takes precedence check order (### before ## before #) -- */
    if (line.startsWith('### ')) {
      flushParagraph();
      elements.push(<h3 key={key++} className="text-lg font-semibold mt-4 mb-2">{line.slice(4)}</h3>);
      continue;
    }
    if (line.startsWith('## ')) {
      flushParagraph();
      elements.push(<h2 key={key++} className="text-xl font-semibold mt-4 mb-2">{line.slice(3)}</h2>);
      continue;
    }
    if (line.startsWith('# ')) {
      flushParagraph();
      elements.push(<h1 key={key++} className="text-2xl font-bold mt-4 mb-2">{line.slice(2)}</h1>);
      continue;
    }

    /* -- Empty line: acts as a paragraph separator -- */
    if (line.trim() === '') {
      flushParagraph();
      continue;
    }

    /**
     * Regular text line: append to the current paragraph with inline formatting.
     * If this is not the first line in the paragraph, insert a space to separate
     * it from the previous line (soft line wrapping).
     */
    if (currentParagraph.length > 0) {
      currentParagraph.push(' ');
    }
    currentParagraph.push(...formatInlineText(line));
  }

  /**
   * Handle an unclosed code block gracefully by rendering whatever content
   * was accumulated, rather than silently dropping it.
   */
  if (inCodeBlock && codeBlockContent.length > 0) {
    elements.push(
      <pre key={key++} className="bg-muted p-4 rounded-md overflow-x-auto">
        <code>{codeBlockContent.join('\n')}</code>
      </pre>
    );
  }

  /* Flush any remaining paragraph content that wasn't followed by a blank line. */
  flushParagraph();

  return <>{elements}</>;
}
