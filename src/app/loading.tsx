export default function Loading() {
  return (
    <div className="max-w-4xl mx-auto px-4 py-12">
      <div className="animate-pulse space-y-4">
        <div className="h-8 bg-muted rounded w-48" />
        <div className="h-4 bg-muted rounded w-72" />
        <div className="space-y-3 mt-8">
          {[1, 2, 3].map((i) => (
            <div key={i} className="h-20 bg-muted rounded" />
          ))}
        </div>
      </div>
    </div>
  );
}
