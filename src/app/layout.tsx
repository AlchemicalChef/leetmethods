import type { Metadata } from 'next';
import localFont from 'next/font/local';
import Link from 'next/link';
import { BookOpen, Code2 } from 'lucide-react';
import './globals.css';

const geistSans = localFont({
  src: './fonts/GeistVF.woff',
  variable: '--font-geist-sans',
  weight: '100 900',
});

const geistMono = localFont({
  src: './fonts/GeistMonoVF.woff',
  variable: '--font-geist-mono',
  weight: '100 900',
});

export const metadata: Metadata = {
  title: 'LeetMethods - Practice Coq Proofs',
  description: 'An interactive platform for practicing formal proofs in Coq',
};

export default function RootLayout({
  children,
}: {
  children: React.ReactNode;
}) {
  return (
    <html lang="en">
      <body className={`${geistSans.variable} ${geistMono.variable} antialiased`}>
        <div className="min-h-screen flex flex-col">
          {/* Navigation */}
          <header className="border-b bg-background/95 backdrop-blur supports-[backdrop-filter]:bg-background/60 sticky top-0 z-50">
            <nav className="max-w-7xl mx-auto px-4 h-16 flex items-center justify-between">
              <Link href="/" className="flex items-center gap-2 font-bold text-xl">
                <Code2 className="h-6 w-6 text-primary" />
                LeetMethods
              </Link>

              <div className="flex items-center gap-6">
                <Link
                  href="/problems"
                  className="text-sm font-medium text-muted-foreground hover:text-foreground transition-colors"
                >
                  Problems
                </Link>
                <Link
                  href="/learn"
                  className="text-sm font-medium text-muted-foreground hover:text-foreground transition-colors flex items-center gap-1"
                >
                  <BookOpen className="h-4 w-4" />
                  Learn
                </Link>
              </div>
            </nav>
          </header>

          {/* Main content */}
          <main className="flex-1">{children}</main>
        </div>
      </body>
    </html>
  );
}
