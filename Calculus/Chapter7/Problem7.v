From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_7 :
  ∃ f1 f2 f3 f4 : ℝ → ℝ,
    f1 ≠ f2 ∧ f1 ≠ f3 ∧ f1 ≠ f4 ∧ f2 ≠ f3 ∧ f2 ≠ f4 ∧ f3 ≠ f4 ∧
    continuous f1 ∧ (∀ x, (f1 x)^2 = x^2) ∧
    continuous f2 ∧ (∀ x, (f2 x)^2 = x^2) ∧
    continuous f3 ∧ (∀ x, (f3 x)^2 = x^2) ∧
    continuous f4 ∧ (∀ x, (f4 x)^2 = x^2) ∧
    (∀ f, continuous f → (∀ x, (f x)^2 = x^2) → f = f1 ∨ f = f2 ∨ f = f3 ∨ f = f4).
Proof.
  exists (λ x, x), (λ x, -x), (λ x, |x|), (λ x, -|x|); repeat split;
  try (intros H1; solve [ apply equal_f with (x := -1) in H1; solve_R | apply equal_f with (x := 1) in H1; solve_R ]);
  try solve [auto_cont].
  intros f H1 H2.

  assert (H3 : ∀ x, f x = x \/ f x = -x) by (intros x; specialize (H2 x); nra).
  assert (H4 : f 0 = 0) by (specialize (H3 0); lra).
  
  assert (H5: f 1 = 1 -> ∀ x, x > 0 -> f x = x).
  { 
    intros H9 x H10. destruct (H3 x) as [H11 | H11]; auto. exfalso.
    pose proof (intermediate_value_theorem_unordered f 1 x 0
      ltac:(apply continuous_imp_continuous_on; exact H1) ltac:(subst; solve_R)) as [c [H12 H13]].
    specialize (H2 c). solve_R.
  }
    
  assert (H6: f 1 = -1 -> ∀ x, x > 0 -> f x = -x).
  { 
    intros H9 x H10. destruct (H3 x) as [H11 | H11]; auto. exfalso.
    pose proof (intermediate_value_theorem_unordered f 1 x 0
      ltac:(apply continuous_imp_continuous_on; exact H1) ltac:(subst; solve_R)) as [c [H12 H13]].
    specialize (H2 c). solve_R.
  }
    
  assert (H7: f (-1) = -1 -> ∀ x, x < 0 -> f x = x).
  { 
    intros H9 x H10. destruct (H3 x) as [H11 | H11]; auto. exfalso.
    pose proof (intermediate_value_theorem_unordered f (-1) x 0
      ltac:(apply continuous_imp_continuous_on; exact H1) ltac:(subst; solve_R)) as [c [H12 H13]].
    specialize (H2 c). solve_R.
  }
    
  assert (H8: f (-1) = 1 -> ∀ x, x < 0 -> f x = -x).
  { 
    intros H9 x H10. destruct (H3 x) as [H11 | H11]; auto. exfalso.
    pose proof (intermediate_value_theorem_unordered f (-1) x 0
      ltac:(apply continuous_imp_continuous_on; exact H1) ltac:(subst; solve_R)) as [c [H12 H13]].
    specialize (H2 c). solve_R.
  }

  destruct (H3 1) as [H9 | H9]; destruct (H3 (-1)) as [H10 | H10].
  - left. extensionality x.
    destruct (Rtotal_order x 0) as [Hx | [Hx | Hx]].
    + apply H7; lra.
    + subst. exact H4.
    + apply H5; lra.
  - right; right; left. extensionality x.
    destruct (Rtotal_order x 0) as [Hx | [Hx | Hx]].
    + rewrite Rabs_left by lra. apply H8; lra.
    + subst. rewrite Rabs_R0. exact H4.
    + rewrite Rabs_right by lra. apply H5; lra.
  - right; right; right. extensionality x.
    destruct (Rtotal_order x 0) as [Hx | [Hx | Hx]].
    + rewrite Rabs_left by lra. rewrite H7 by lra. lra.
    + subst. rewrite Rabs_R0, H4. lra.
    + rewrite Rabs_right by lra. apply H6; lra.
  - right; left. extensionality x.
    destruct (Rtotal_order x 0) as [Hx | [Hx | Hx]].
    + apply H8; lra.
    + subst. rewrite H4. lra.
    + apply H6; lra.
Qed.
