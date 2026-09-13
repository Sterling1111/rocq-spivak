From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_16_a : ∀ f a b,
  a < b ->
  continuous_on f (a, b) ->
  (∀ M, ∃ δ, δ > 0 /\ ∀ x, a < x < a + δ -> f x > M) ->
  (∀ M, ∃ δ, δ > 0 /\ ∀ x, b - δ < x < b -> f x > M) ->
  ∃ y, y ∈ (a, b) /\ ∀ x, x ∈ (a, b) -> f y <= f x.
Proof.
  intros f a b H1 H2 H3 H4.
  set (c := (a + b) / 2).
  destruct (H3 (f c)) as [δ1 [H5 H6]].
  destruct (H4 (f c)) as [δ2 [H7 H8]].
  set (u := a + Rmin (δ1 / 2) ((b - a) / 4)).
  set (v := b - Rmin (δ2 / 2) ((b - a) / 4)).
  assert (H9 : a < u /\ u < c /\ c < v /\ v < b).
  { unfold u, v, c. solve_R. }
  assert (H10 : continuous_on f [u, v]).
  { apply continuous_on_subset with (A2 := (a, b)); auto. intros x H10. solve_R. }
  destruct (continuous_on_interval_attains_minimum f u v ltac:(lra) H10)
    as [y [H11 H12]].
  exists y. split; [solve_R |]. intros x H13.
  pose proof (H12 c ltac:(solve_R)) as H14.
  destruct (Rlt_dec x u) as [H15 | H15].
  - specialize (H6 x ltac:(unfold u in H15; solve_R)). lra.
  - destruct (Rlt_dec v x) as [H16 | H16].
    + specialize (H8 x ltac:(unfold v in H16; solve_R)). lra.
    + apply H12. solve_R.
Qed.
