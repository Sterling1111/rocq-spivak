From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_3_a : ∀ f a b,
  continuous_on f [a, b] ->
  a < b ->
  f a < 0 /\ 0 < f b ->
  ∃ x, x ∈ [a, b] /\ f x = 0 /\ (∀ y, y ∈ [a, b] -> f y = 0 -> y <= x).
Proof.
  intros f a b H1 H2 H3.
  set (g := fun x => - f (a + b - x)).
  assert (H4 : continuous_on g [a, b]).
  { apply continuous_on_neg, continuous_on_comp with (D2 := [a, b]); auto_cont. }
  assert (H5 : g a < 0 < g b).
  { unfold g. rewrite Rplus_minus_l, Rplus_minus_r. lra. }
  destruct (intermediate_value_theorem_smallest_zero g a b H4 H2 H5) as [z [H7 [H8 H9]]].
  exists (a + b - z).
  repeat split; try solve [ solve_R ].
  - unfold g in H8. lra.
  - intros y H10 H11.
    assert (H13 : g (a + b - y) = 0).
    { unfold g. replace (a + b - (a + b - y)) with y by lra. lra. }
    specialize (H9 (a + b - y) ltac:(solve_R) H13).
    lra. 
Qed.

Lemma lemma_8_3_b : ∀ f a b,
  continuous_on f [a, b] ->
  a < b ->
  f a < 0 /\ 0 < f b ->
  ∃ x, is_lub (fun y => a <= y /\ y <= b /\ f y < 0) x /\ f x = 0.
Proof.
  intros f a b H1 H2 H3.
  
Admitted.