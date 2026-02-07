'use client';

import { TutorialPage } from '@/components/tutorial/TutorialPage';
import { tutorialSteps } from '@/lib/tutorial/tutorial-steps';

export default function Tutorial() {
  return (
    <TutorialPage
      steps={tutorialSteps}
      title="Tutorial: Basics"
      storageKey="leetmethods-tutorial-progress"
      completionLink={{ href: '/tutorial/applied-methods', label: 'Continue to Applied Methods' }}
    />
  );
}
