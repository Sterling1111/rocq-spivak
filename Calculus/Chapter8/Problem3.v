From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_3_a : ∀ f a b,
  continuous_on f [a, b] ->
  a < b ->
  f a < 0 /\ 0 < f b ->
  ∃ x, x ∈ [a, b] /\ f x = 0 /\ (∀ y, y ∈ [a, b] -> f y = 0 -> y <= x).
Proof.
  intros f a b H1 H2 H3.
  set (g := λ x, - f (a + b - x)).
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
  ∃ x, is_lub (λ y, a <= y /\ y <= b /\ f y < 0) x /\ f x = 0.
Proof.
  intros f a b H1 H2 [H3 H4].
  set (A := λ y, a <= y /\ y <= b /\ f y < 0).
  assert (H5 : has_upper_bound A).
  { exists b. intros y [H5 [H6 H7]]. exact H6. }
  assert (H6 : A ≠ ∅).
  { apply not_Empty_In. exists a. repeat split; lra. }
  destruct (completeness_upper_bound A H5 H6) as [c H7].
  assert (H8 : a <= c <= b).
  { destruct H7 as [H7 H8]. split.
    - apply H7. repeat split; lra.
    - apply H8. intros y [H9 [H10 H11]]. exact H10. }
  exists c. split; [exact H7 |].
  destruct (Rlt_dec (f c) 0) as [H9 | H9].
  - assert (H10 : c < b).
    { destruct (Req_dec c b); [subst; lra | lra]. }
    destruct (H1 c ltac:(solve_R) (- f c) ltac:(lra)) as [δ [H11 H12]].
    set (x := c + Rmin δ (b - c) / 2).
    assert (H13 : c < x <= b) by (unfold x; solve_R).
    assert (H14 : |x - c| < δ) by (unfold x; solve_R).
    specialize (H12 x ltac:(solve_R) ltac:(solve_R)).
    assert (H15 : x ∈ A) by (repeat split; solve_R).
    destruct H7 as [H7 _]. specialize (H7 x H15). lra.
  - destruct (Req_dec (f c) 0) as [H10 | H10]; auto.
    destruct (H1 c ltac:(solve_R) (f c) ltac:(lra)) as [δ [H11 H12]].
    destruct (exists_point_within_delta A c δ H7 H11) as [x [H13 H14]].
    destruct H13 as [H13 [H15 H16]].
    assert (H17 : x <> c) by (intros H17; subst; lra).
    specialize (H12 x ltac:(solve_R) ltac:(solve_R)). solve_R.
Qed.