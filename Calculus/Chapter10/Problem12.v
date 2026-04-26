From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_12 : ∀ g g' x,
  g x ≠ 0 ->
  ⟦ der ⟧ g = g' ->
  ⟦ der x ⟧ (λ x, 1 / g x) = (λ x, - g' x / (g x)^2).
Proof.
  intros g g' x H1 H2.
  set (f := λ y, 1 / y).
  set (f' := λ y, -1 / y^2).
  assert (H3 : ⟦ der (g x) ⟧ f = f').
  { unfold f, f'. auto_diff. }
  assert (H4 : ⟦ der x ⟧ g = g') by apply H2.
  pose proof derivative_at_comp g f g' f' x H4 H3 as H5.
  apply derivative_at_ext_val with (f' := (f' ∘ g ⋅ g')%function); auto.
  unfold f', compose, mult. field. apply H1.
Qed.