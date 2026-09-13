From Calculus.Chapter14 Require Import Prelude.

Lemma lemma_14_3_a : ∀ x,
  x > 0 ->
  ⟦ der x ⟧ (λ x, ∫ 0 x (λ t, 1 / (1 + t^2)) + ∫ 0 (1/x) (λ t, 1 / (1 + t^2))) = (λ _, 0).
Proof.
  intros x H1.
  set (g := λ t, 1 / (1 + t^2)).
  set (G := λ u, ∫ 0 u g).
  set (H := λ x, 1 / x).
  set (H' := λ x, -1 / x^2).

  assert (H2 : ⟦ der ⟧ G = g).
  { unfold G, g. apply FTC1_global. auto_cont. }

  assert (H3 : ⟦ der x ⟧ H = H').
  { unfold H, H'. auto_diff. }

  change (⟦ der x ⟧ (G + (G ∘ H)) = (λ _, 0)).

  eapply derivative_at_ext_val with (f' := (g + ((g ∘ H) ⋅ H'))%function).

  - apply derivative_at_plus; auto.
    apply derivative_at_comp; auto.
  - unfold g, H, H', compose. solve_R.
Qed.

Lemma lemma_14_3_b : ∀ x,
  0 < x < PI/2 ->
  ⟦ der x ⟧ (λ x, ∫ (-(cos x)) (sin x) (λ t, 1 / √(1 - t^2))) =
    (λ _, 0).
Abort.
