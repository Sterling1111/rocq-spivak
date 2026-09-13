From Calculus.Chapter8 Require Import Prelude.
From Lib Require Import Rational.

Lemma lemma_8_5_a : ∀ x y, y - x > 1 -> ∃ k : ℤ, x < k < y.
Proof.
  intros x y H1.
  set (A := λ l, is_integer l /\ l <= x).

  assert (H2 : has_upper_bound A).
  { exists (x + 1). intros z [_ H2]. solve_R. }

  assert (H3 : A ≠ ⦃⦄).
  {
    apply not_Empty_In. destruct (INR_unbounded (- x)) as [n H3].
    exists (- n).
    split.
    - unfold is_integer. exists (- Z.of_nat n)%Z.
      rewrite opp_IZR, <- INR_IZR_INZ.
      reflexivity.
    - lra.
  }
  
  pose proof completeness_upper_bound A H2 H3 as [sup [H4 H5]].

  assert (H6 : ¬ is_upper_bound A (sup - 1)).
  { intros H6. specialize (H5 (sup - 1) H6). lra. }

  apply not_all_ex_not in H6 as [z H6].
  apply imply_to_and in H6 as [[[l H6] H7] H8].
  apply Rnot_le_lt in H8.
  

  exists (l + 1)%Z.
  rewrite plus_IZR, <- H6.
  split; [ | lra ].
  apply Rnot_le_lt. intros H9.
  assert (H10 : (z + 1) ∈ A).
  { split; auto. exists (l + 1)%Z. rewrite plus_IZR, <- H6. reflexivity. }
  specialize (H4 (z + 1) H10).
  lra.
Qed.

Lemma lemma_8_5_b : ∀ x y, x < y -> ∃ r, rational r /\ x < r < y.
Proof.
  intros x y H1. pose proof exists_nat_gt_inv_scale 0 1 (y - x) ltac:(lra) ltac:(lra) as [n [H2 H3]].
  rewrite Rminus_0_r in H3.
  apply Rmult_lt_compat_r with (r := n) in H3; field_simplify in H3; solve_R.
  pose proof lemma_8_5_a (n * x) (n * y) H3 as [r [H4 H5]].
  exists (r / n). split.
  - exists r, (Z.of_nat n). rewrite INR_IZR_INZ. reflexivity.
  - split; apply Rmult_lt_reg_r with (r := n); auto; field_simplify; solve_R.
Qed.

Lemma lemma_8_5_c : ∀ r s, rational r -> rational s -> r < s -> ∃ t, irrational t /\ r < t < s.
Proof.
  intros r s H1 H2 H3.
  exists (r + √(2) * (s - r) / 2).
  split.
  - unfold irrational. intros H4.
    assert (H5 : √(2) = 2 * ((r + √(2) * (s - r) / 2) - r) / (s - r)) by solve_R.
    assert_rational (2 * (r + √2 * (s - r) / 2 - r) / (s - r)) H6.
    assert (rational (√2)) as H7. { rewrite H5; auto. }
    pose proof sqrt_2_irrational as H8.
    unfold irrational, not in H8. apply H8, H7.
  - pose proof sqrt_lt_R0 2 ltac:(lra) as H4. pose proof sqrt_sqrt 2 ltac:(lra) as H5.
    nra.
Qed.

Lemma lemma_8_5_d : ∀ x y, x < y -> ∃ t : ℝ, irrational t /\ x < t < y.
Proof.
  intros x y H1.
  pose proof lemma_8_5_b x y H1 as [r [H2 H3]].
  pose proof lemma_8_5_b r y ltac:(lra) as [s [H4 H5]].
  pose proof lemma_8_5_c r s H2 H4 ltac:(lra) as [t [H6 H7]].
  exists t; split; solve_R.
Qed.