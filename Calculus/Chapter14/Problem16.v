From Calculus.Chapter14 Require Import Prelude.

Lemma lemma_14_16_a : ∀ x b F' G',
  let F := λ x, ∫ 1 x (λ t, 1 / t) in
  let G := λ x, ∫ b (b * x) (λ t, 1 / t) in
  ⟦ der ⟧ F = F' ->
  ⟦ der ⟧ G = G' ->
  x > 0 ->
  b > 0 ->
  F' x = 1 / x /\ G' x = 1 / x.
Proof.
  intros x b F' G' F B H1 H2 H3 H4.
  split.
  - apply (derivative_at_unique F F' (λ y : ℝ, 1 / y) x).
    + auto.
    + unfold F. apply FTC1_at with (c := Rmin 1 x / 2) (d := Rmax 1 x + 1); auto_cont.
  - assert (H5 : ⟦ der (b * x) ⟧ (λ y, ∫ b y (λ t, 1 / t)) = (λ y, 1 / y)).
    { apply FTC1_at with (c := Rmin b (b * x) / 2) (d := Rmax b (b * x) + 1); auto_cont. }
    apply (derivative_at_unique B G' (λ y, 1 / y) x); auto.
    unfold B.
    apply derivative_at_ext_val with (f' := λ y, 1 / (b * y) * b).
    + apply (derivative_at_comp (λ y, b * y) (λ y, ∫ b y (λ t, 1 / t))
        (λ _, b) (λ y, 1 / y) x); [auto_diff | exact H5].
    + field. split; lra.
Qed.

Lemma lemma_14_16_b : ∀ a b,
  a > 0 -> b > 0 ->
  ∫ 1 a (λ t, 1 / t) + ∫ 1 b (λ t, 1 / t) = ∫ 1 (a * b) (λ t, 1 / t).
Proof.
  intros a b H1 H2.
  set (F := λ x, ∫ 1 x (λ t, 1 / t)).
  set (G := λ x, ∫ b (b * x) (λ t, 1 / t)).
  assert (H3 : ∀ x, x > 0 -> ⟦ der x ⟧ (λ y, F y - G y) = (λ _, 0)).
  {
    intros x H3.
    assert (H4 : ⟦ der x ⟧ F = (λ y, 1 / y)).
    { unfold F. apply FTC1_at with (c := Rmin 1 x / 2) (d := Rmax 1 x + 1); auto_cont. }
    assert (H5 : ⟦ der (b * x) ⟧ (λ y, ∫ b y (λ t, 1 / t)) = (λ y, 1 / y)).
    { apply FTC1_at with (c := Rmin b (b * x) / 2) (d := Rmax b (b * x) + 1); auto_cont. }
    assert (H6 : ⟦ der x ⟧ G = (λ y, 1 / y)).
    {
      unfold G. apply derivative_at_ext_val with (f' := λ y, 1 / (b * y) * b).
      - apply (derivative_at_comp (λ y, b * y) (λ y, ∫ b y (λ t, 1 / t))
          (λ _, b) (λ y, 1 / y) x); [auto_diff | exact H5].
      - field. split; lra.
    }
    auto_diff.
  }
  assert (H4 : ⟦ der ⟧ (λ y, F y - G y)
    [Rmin 1 a / 2, Rmax 1 a + 1] = (λ _, 0)).
  {
    apply derivative_at_imp_derivative_on.
    - apply differentiable_domain_closed. solve_R.
    - intros x H4. apply H3. solve_R.
  }
  pose proof derivative_zero_imp_const (λ y, F y - G y)
    (Rmin 1 a / 2) (Rmax 1 a + 1) ltac:(solve_R) H4 as [c H5].
  pose proof H5 1 ltac:(solve_R) as H6.
  pose proof H5 a ltac:(solve_R) as H7.
  unfold F, G in H6, H7.
  rewrite Rmult_1_r, !integral_n_n in H6.
  assert (H8 : ∫ 1 (a * b) (λ t, 1 / t) =
    ∫ 1 b (λ t, 1 / t) + ∫ b (a * b) (λ t, 1 / t)).
  {
    apply integral_split'. apply theorem_13_3; [solve_R | auto_cont].
  }
  replace (b * a) with (a * b) in H7 by ring. lra.
Qed.
