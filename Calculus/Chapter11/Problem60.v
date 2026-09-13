From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_60_a : ∀ f f' a b,
  a < b ->
  ⟦ der ⟧ f [a, b] = f' ->
  minimum_point f [a, b] a ->
  f' a >= 0.
Proof.
  intros f f' a b H1 H2 [_ H3].
  pose proof derivative_on_imp_derivative_at_right f f' [a, b] a ltac:(auto_interval) H2 as H4.
  destruct (Rlt_dec (f' a) 0) as [H5 | H5]; try lra.
  destruct (H4 (- f' a) ltac:(lra)) as [δ [H6 H7]].
  set (h := Rmin δ (b - a) / 2).
  assert (H8 : 0 < h < δ /\ (a + h) ∈ [a, b]) by (unfold h; solve_R).
  specialize (H7 h ltac:(solve_R)). specialize (H3 (a + h) ltac:(solve_R)).
  assert (H9 : 0 <= (f (a + h) - f a) / h) by (apply Rmult_le_pos; [solve_R | apply Rlt_le, Rinv_0_lt_compat; solve_R]).
  solve_R.
Qed.

Lemma minimum_right_endpoint_nonpos : ∀ f f' a b,
  a < b ->
  ⟦ der ⟧ f [a, b] = f' ->
  minimum_point f [a, b] b ->
  f' b <= 0.
Proof.
  intros f f' a b H1 H2 [_ H3].
  pose proof derivative_on_imp_derivative_at_left f f' [a, b] b ltac:(auto_interval) H2 as H4.
  destruct (Rlt_dec 0 (f' b)) as [H5 | H5]; try lra.
  destruct (H4 (f' b) H5) as [δ [H6 H7]].
  set (h := - Rmin δ (b - a) / 2).
  assert (H8 : 0 < -h < δ /\ (b + h) ∈ [a, b]) by (unfold h; solve_R).
  specialize (H7 h ltac:(solve_R)). specialize (H3 (b + h) ltac:(solve_R)).
  assert (H9 : (f (b + h) - f b) / h <= 0).
  { apply Rmult_le_reg_r with (r := -h); solve_R. }
  solve_R.
Qed.

Lemma lemma_11_60_b : ∀ f f' a b,
  a < b ->
  ⟦ der ⟧ f [a, b] = f' ->
  f' a < 0 -> f' b > 0 ->
  ∃ x, x ∈ (a, b) /\ f' x = 0.
Proof.
  intros f f' a b H1 H2 H3 H4.
  assert (H5 : continuous_on f [a, b]).
  { apply differentiable_on_imp_continuous_on_closed; auto. apply derivative_on_imp_differentiable_on with (f' := f'); auto. }
  pose proof continuous_on_interval_attains_minimum f a b H1 H5 as [x H6].
  assert (H7 : x ∈ (a, b)).
  {
    destruct H6 as [H6 H7].
    assert (x = a \/ x = b \/ x ∈ (a, b)) as [H8 | [H8 | H8]] by solve_R; auto; subst.
    - pose proof lemma_11_60_a f f' a b H1 H2 ltac:(split; auto) as H8. lra.
    - pose proof minimum_right_endpoint_nonpos f f' a b H1 H2 ltac:(split; auto) as H8. lra.
  }
  pose proof derivative_on_imp_derivative_at f f' [a, b] x ltac:(auto_interval) H2 as H8.
  assert (H9 : minimum_point f (a, b) x).
  { split; auto. intros y H9. apply H6. solve_R. }
  pose proof derivative_at_minimum_point_zero f a b x H9
    ltac:(apply derivative_at_imp_differentiable_at with (f' := f'); auto) as H10.
  exists x. split; auto. exact (derivative_at_unique f _ _ x H8 H10).
Qed.

Lemma lemma_11_60_c : ∀ f f' a b c,
  a < b ->
  ⟦ der ⟧ f [a, b] = f' ->
  (f' a < c /\ c < f' b) \/ (f' b < c /\ c < f' a) ->
  ∃ x, x ∈ (a, b) /\ f' x = c.
Proof.
  intros f f' a b c H1 H2 [H3 | H3].
  - set (g := λ x, f x - c * x).
    assert (H4 : ⟦ der ⟧ g [a, b] = λ x, f' x - c).
    {
      unfold g. apply derivative_on_minus_closed; auto.
      auto_diff.
    }
    pose proof lemma_11_60_b g (λ x, f' x - c) a b H1 H4 ltac:(lra) ltac:(lra) as [x [H5 H6]].
    exists x. split; auto. lra.
  - set (g := λ x, c * x - f x).
    assert (H4 : ⟦ der ⟧ g [a, b] = λ x, c - f' x).
    {
      unfold g. apply derivative_on_minus_closed; auto.
      auto_diff.
    }
    pose proof lemma_11_60_b g (λ x, c - f' x) a b H1 H4 ltac:(lra) ltac:(lra) as [x [H5 H6]].
    exists x. split; auto. lra.
Qed.
