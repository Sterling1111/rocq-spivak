From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_21 : ∀ f f_inv F G f',
  one_to_one f ->
  differentiable f ->
  ⟦ der ⟧ f = f' ->
  (∀ x, f' x <> 0) ->
  inverse f f_inv ->
  ⟦ der ⟧ F = f ->
  G = (λ x, x * f_inv x - F (f_inv x)) ->
  ⟦ der ⟧ G = f_inv.
Proof.
  intros f f_inv F G f' H1 H2 H3 H4 H5 H6 H7.
  assert (H8 : ⟦ der ⟧ f_inv = λ x, / f' (f_inv x)).
  { apply global_inverse_theorem with (f := f); auto. }
  pose proof inverse_spec f f_inv H5 as [H9 H10].
  assert (H11 : ⟦ der ⟧ (λ x, x * f_inv x - F (f_inv x)) =
    λ x, f_inv x + x * / f' (f_inv x) - f (f_inv x) * / f' (f_inv x)) by auto_diff.
  replace f_inv with (λ x, f_inv x + x * / f' (f_inv x) - f (f_inv x) * / f' (f_inv x)) at 1.
  - rewrite H7. exact H11.
  - extensionality x. rewrite H10. ring.
Qed.
