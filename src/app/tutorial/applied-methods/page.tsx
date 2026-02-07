'use client';

import { TutorialPage } from '@/components/tutorial/TutorialPage';
import { appliedMethodsSteps } from '@/lib/tutorial/applied-methods-steps';

export default function AppliedMethodsTutorial() {
  return (
    <TutorialPage
      steps={appliedMethodsSteps}
      title="Tutorial: Applied Methods"
      storageKey="leetmethods-applied-methods-progress"
      completionLink={{ href: '/problems', label: 'Start Solving Problems' }}
    />
  );
}
