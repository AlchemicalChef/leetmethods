'use client';

import { useState, useCallback } from 'react';
import { Button } from '@/components/ui/button';
import { Card } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';
import {
  Select,
  SelectContent,
  SelectItem,
  SelectTrigger,
  SelectValue,
} from '@/components/ui/select';
import { Plus, Trash2, CheckCircle2, Loader2, AlertCircle } from 'lucide-react';
import type { Difficulty, Category } from '@/lib/problems/types';

interface CustomProblemFormData {
  title: string;
  difficulty: Difficulty;
  category: Category;
  tags: string;
  description: string;
  prelude: string;
  template: string;
  solution: string;
  hints: string[];
}

interface CustomProblemFormProps {
  initialData?: CustomProblemFormData;
  onSave: (data: CustomProblemFormData) => void;
  onCancel: () => void;
  isEditing?: boolean;
}

const defaultData: CustomProblemFormData = {
  title: '',
  difficulty: 'easy',
  category: 'logic',
  tags: '',
  description: '',
  prelude: '',
  template: 'Theorem my_theorem : True.\nProof.\n  (* Your proof here *)\nAdmitted.',
  solution: 'Theorem my_theorem : True.\nProof.\n  exact I.\nQed.',
  hints: [''],
};

export function CustomProblemForm({ initialData, onSave, onCancel, isEditing = false }: CustomProblemFormProps) {
  const [data, setData] = useState<CustomProblemFormData>(initialData ?? defaultData);
  const [verified, setVerified] = useState(false);
  const [verifying, setVerifying] = useState(false);
  const [verifyError, setVerifyError] = useState<string | null>(null);
  const [errors, setErrors] = useState<Record<string, string>>({});

  const updateField = useCallback(<K extends keyof CustomProblemFormData>(key: K, value: CustomProblemFormData[K]) => {
    setData((prev) => ({ ...prev, [key]: value }));
    setVerified(false);
    setErrors((prev) => {
      const next = { ...prev };
      delete next[key];
      return next;
    });
  }, []);

  const addHint = () => {
    setData((prev) => ({ ...prev, hints: [...prev.hints, ''] }));
  };

  const updateHint = (index: number, value: string) => {
    setData((prev) => {
      const hints = [...prev.hints];
      hints[index] = value;
      return { ...prev, hints };
    });
  };

  const removeHint = (index: number) => {
    setData((prev) => ({
      ...prev,
      hints: prev.hints.filter((_, i) => i !== index),
    }));
  };

  const validate = (): boolean => {
    const newErrors: Record<string, string> = {};
    if (data.title.trim().length < 3) {
      newErrors.title = 'Title must be at least 3 characters';
    }
    if (!data.template.trim()) {
      newErrors.template = 'Template is required';
    }
    if (!data.solution.includes('Qed.')) {
      newErrors.solution = 'Solution must contain Qed.';
    }
    setErrors(newErrors);
    return Object.keys(newErrors).length === 0;
  };

  const handleVerify = async () => {
    if (!validate()) return;
    setVerifying(true);
    setVerifyError(null);

    try {
      // Dynamically import CoqService to avoid SSR issues
      const { getCoqService } = await import('@/lib/coq');
      const service = getCoqService({
        onStatusChange: () => {},
        onGoalsUpdate: () => {},
        onMessage: () => {},
        onPositionChange: () => {},
        onReady: () => {},
        onError: () => {},
      });
      await service.initialize();
      const result = await service.verify(data.prelude, data.solution, ['admit', 'Admitted']);
      if (result.success) {
        setVerified(true);
        setVerifyError(null);
      } else {
        setVerifyError(result.errors.join('; ') || 'Solution verification failed');
      }
    } catch (err) {
      setVerifyError(err instanceof Error ? err.message : 'Verification failed');
    } finally {
      setVerifying(false);
    }
  };

  const handleSave = () => {
    if (!validate()) return;
    if (!verified && !isEditing) return;
    onSave(data);
  };

  return (
    <div className="space-y-8">
      {/* Section 1: Metadata */}
      <Card className="p-6">
        <h3 className="text-lg font-semibold mb-4">Problem Metadata</h3>
        <div className="space-y-4">
          <div>
            <label className="block text-sm font-medium mb-1">Title *</label>
            <input
              type="text"
              value={data.title}
              onChange={(e) => updateField('title', e.target.value)}
              className="w-full px-3 py-2 border rounded-md bg-background"
              placeholder="e.g., Prove Modus Ponens"
            />
            {errors.title && <p className="text-xs text-red-500 mt-1">{errors.title}</p>}
          </div>

          <div className="grid grid-cols-2 gap-4">
            <div>
              <label className="block text-sm font-medium mb-1">Difficulty</label>
              <Select value={data.difficulty} onValueChange={(v) => updateField('difficulty', v as Difficulty)}>
                <SelectTrigger>
                  <SelectValue />
                </SelectTrigger>
                <SelectContent>
                  <SelectItem value="easy">Easy</SelectItem>
                  <SelectItem value="medium">Medium</SelectItem>
                  <SelectItem value="hard">Hard</SelectItem>
                </SelectContent>
              </Select>
            </div>
            <div>
              <label className="block text-sm font-medium mb-1">Category</label>
              <Select value={data.category} onValueChange={(v) => updateField('category', v as Category)}>
                <SelectTrigger>
                  <SelectValue />
                </SelectTrigger>
                <SelectContent>
                  <SelectItem value="logic">Logic</SelectItem>
                  <SelectItem value="induction">Induction</SelectItem>
                  <SelectItem value="lists">Lists</SelectItem>
                  <SelectItem value="arithmetic">Arithmetic</SelectItem>
                  <SelectItem value="data-structures">Data Structures</SelectItem>
                  <SelectItem value="relations">Relations</SelectItem>
                </SelectContent>
              </Select>
            </div>
          </div>

          <div>
            <label className="block text-sm font-medium mb-1">Tags (comma-separated)</label>
            <input
              type="text"
              value={data.tags}
              onChange={(e) => updateField('tags', e.target.value)}
              className="w-full px-3 py-2 border rounded-md bg-background"
              placeholder="e.g., basic, implication"
            />
          </div>

          <div>
            <label className="block text-sm font-medium mb-1">Description</label>
            <textarea
              value={data.description}
              onChange={(e) => updateField('description', e.target.value)}
              className="w-full px-3 py-2 border rounded-md bg-background min-h-[100px]"
              placeholder="Describe the problem..."
            />
          </div>
        </div>
      </Card>

      {/* Section 2: Coq Code */}
      <Card className="p-6">
        <h3 className="text-lg font-semibold mb-4">Coq Code</h3>
        <div className="space-y-4">
          <div>
            <label className="block text-sm font-medium mb-1">Prelude (read-only imports)</label>
            <textarea
              value={data.prelude}
              onChange={(e) => updateField('prelude', e.target.value)}
              className="w-full px-3 py-2 border rounded-md bg-background font-mono text-sm min-h-[80px]"
              placeholder="Require Import Arith."
            />
          </div>

          <div>
            <label className="block text-sm font-medium mb-1">Template * (initial code for solver)</label>
            <textarea
              value={data.template}
              onChange={(e) => updateField('template', e.target.value)}
              className="w-full px-3 py-2 border rounded-md bg-background font-mono text-sm min-h-[120px]"
            />
            {errors.template && <p className="text-xs text-red-500 mt-1">{errors.template}</p>}
          </div>

          <div>
            <label className="block text-sm font-medium mb-1">Solution * (reference proof)</label>
            <textarea
              value={data.solution}
              onChange={(e) => updateField('solution', e.target.value)}
              className="w-full px-3 py-2 border rounded-md bg-background font-mono text-sm min-h-[120px]"
            />
            {errors.solution && <p className="text-xs text-red-500 mt-1">{errors.solution}</p>}
          </div>
        </div>
      </Card>

      {/* Section 3: Hints */}
      <Card className="p-6">
        <h3 className="text-lg font-semibold mb-4">Hints</h3>
        <div className="space-y-2">
          {data.hints.map((hint, index) => (
            <div key={index} className="flex items-center gap-2">
              <span className="text-xs text-muted-foreground w-6">{index + 1}.</span>
              <input
                type="text"
                value={hint}
                onChange={(e) => updateHint(index, e.target.value)}
                className="flex-1 px-3 py-2 border rounded-md bg-background text-sm"
                placeholder="Enter a hint..."
              />
              <Button variant="ghost" size="sm" onClick={() => removeHint(index)}>
                <Trash2 className="h-3 w-3" />
              </Button>
            </div>
          ))}
          <Button variant="outline" size="sm" onClick={addHint}>
            <Plus className="h-3 w-3 mr-1" />
            Add Hint
          </Button>
        </div>
      </Card>

      {/* Section 4: Verification & Save */}
      <Card className="p-6">
        <h3 className="text-lg font-semibold mb-4">Verify & Save</h3>
        <div className="space-y-3">
          <div className="flex items-center gap-3">
            <Button
              onClick={handleVerify}
              disabled={verifying}
              variant="outline"
            >
              {verifying ? (
                <Loader2 className="h-4 w-4 mr-1 animate-spin" />
              ) : verified ? (
                <CheckCircle2 className="h-4 w-4 mr-1 text-green-500" />
              ) : (
                <AlertCircle className="h-4 w-4 mr-1" />
              )}
              {verifying ? 'Verifying...' : verified ? 'Verified' : 'Test Solution'}
            </Button>
            {verified && (
              <Badge className="bg-green-100 text-green-800 dark:bg-green-900 dark:text-green-200">
                Solution passes
              </Badge>
            )}
          </div>
          {verifyError && (
            <p className="text-sm text-red-500">{verifyError}</p>
          )}
          <div className="flex items-center gap-3 pt-2">
            <Button
              onClick={handleSave}
              disabled={!verified && !isEditing}
              className="bg-green-600 hover:bg-green-700"
            >
              {isEditing ? 'Save Changes' : 'Create Problem'}
            </Button>
            <Button variant="outline" onClick={onCancel}>
              Cancel
            </Button>
          </div>
          {!verified && !isEditing && (
            <p className="text-xs text-muted-foreground">Test the solution before saving</p>
          )}
        </div>
      </Card>
    </div>
  );
}
