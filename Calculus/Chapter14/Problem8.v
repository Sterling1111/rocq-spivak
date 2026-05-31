From Calculus.Chapter14 Require Import Prelude.

Lemma lemma_14_8 : ∀ f x,
  continuous f ->
  ⟦ der x ⟧ (λ x, ∫ 0 x (λ t, x * f t)) =
    (λ x, ∫ 0 x f + x * f x).
Proof.
  intros f x H1. 
  replace (λ x0 : ℝ, ∫ 0 x0 (λ t : ℝ, x0 * f t)) with ((λ x0 : ℝ, x0) ⋅ (λ x0 : ℝ, ∫ 0 x0 f))%function.
  2 : {
    extensionality y.
    rewrite integral_mult_scalar'; auto.
    apply theorem_13_3; auto_cont. 
  }
  replace (λ x0 : ℝ, ∫ 0 x0 f + x0 * f x0) with ((λ _ : ℝ, 1) ⋅ (λ x0 : ℝ, ∫ 0 x0 f) + (λ x0 : ℝ, x0) ⋅ f)%function.
  2 : { extensionality y. lra. }
  apply derivative_at_mult; [ auto_diff | apply FTC1_global; auto ].
Qed.