From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_49 : ∀ f f' g g' a b,
  a < b ->
  continuous_on f [a, b] -> continuous_on g [a, b] ->
  ⟦ der ⟧ f (a, b) = f' -> ⟦ der ⟧ g (a, b) = g' ->
  g a <> g b ->
  (∀ x, x ∈ (a, b) -> f' x <> 0 \/ g' x <> 0) ->
  ∃ x, x ∈ (a, b) /\ (f b - f a) / (g b - g a) = f' x / g' x.
Proof.
  intros f f' g g' a b H1 H2 H3 H4 H5 H6 H7.
  pose proof cauchy_mean_value_theorem f f' g g' a b H1 H2 H3 H4 H5 as [x [H8 H9]].
  assert (H10 : g' x <> 0).
  { intros H10. destruct (H7 x H8) as [H11 | H11]; nra. }
  exists x. split; auto. solve_R.
Qed.
