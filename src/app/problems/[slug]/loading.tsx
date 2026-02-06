export default function ProblemLoading() {
  return (
    <div className="h-[calc(100vh-64px)] flex items-center justify-center">
      <div className="flex items-center gap-3 text-muted-foreground">
        <div className="animate-spin rounded-full h-5 w-5 border-2 border-primary border-t-transparent" />
        <span>Loading problem...</span>
      </div>
    </div>
  );
}
