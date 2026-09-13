From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_39_i : ⟦ lim ∞ ⟧ (λ x, (x^3 + 4*x - 7) / (7*x^2 - x + 1)) = ∞.
Proof.
  intros M. exists (Rmax 2 (14 * (|M| + 1))). intros x H1.
  assert (H2 : x > 2 /\ x > 14 * (|M| + 1)) by solve_R.
  assert (H3 : 0 < 7*x^2 - x + 1 <= 7*x^2) by nra.
  assert (H4 : x^3 / 2 < x^3 + 4*x - 7) by nra.
  assert (H5 : (|M| + 1) * (7*x^2 - x + 1) < x^3 / 2).
  { pose proof (Rabs_pos M) as H5.
    assert (H6 : (|M| + 1) * (7*x^2 - x + 1) <= (|M| + 1) * (7*x^2)) by nra.
    assert (H7 : 0 < x^2) by nra. nra. }
  apply Rmult_lt_reg_r with (r := 7*x^2 - x + 1); try lra.
  field_simplify; try lra. pose proof (Rle_abs M) as H6. nra.
Qed.

Lemma lemma_5_39_ii : ⟦ lim ∞ ⟧ (λ x, x * (1 + (sin x)^2)) = ∞.
Proof.
  intros M. exists (Rmax 0 M). intros x H1.
  pose proof (pow2_ge_0 (sin x)) as H2. solve_R.
Qed.

Lemma lemma_5_39_iii : ¬ ∃ L, ⟦ lim ∞ ⟧ (λ x, x * (sin x)^2) = L.
Proof.
  intros [L H1]. specialize (H1 (1/2) ltac:(lra)) as [N H2].
  destruct (INR_unbounded (Rmax N 2 / π)) as [n H3].
  pose proof π_pos as H4.
  assert (H5 : n * π > Rmax N 2).
  { apply Rmult_lt_compat_r with (r := π) in H3; auto. field_simplify in H3; lra. }
  specialize (H2 (n * π) ltac:(solve_R)) as H6.
  rewrite sin_n_pi in H6.
  specialize (H2 (n * π + π/2) ltac:(solve_R)) as H7.
  assert (H8 : (sin (n * π + π/2))^2 = 1).
  { rewrite sin_plus, sin_π_over_2, cos_π_over_2, sin_n_pi.
    pose proof (pythagorean_identity (n * π)) as H8. rewrite sin_n_pi in H8. nra. }
  rewrite H8 in H7. solve_R.
Qed.

Lemma lemma_5_39_iv : ⟦ lim ∞ ⟧ (λ x, x^2 * sin (1 / x)) = ∞.
Proof.
  pose proof limit_sin_x_over_x as H1.
  specialize (H1 (1/2) ltac:(lra)) as [δ [H2 H3]].
  intros M. exists (Rmax (1 / δ) (2 * (|M| + 1))). intros x H4.
  assert (H5 : x > 0 /\ x > 1 / δ) by solve_R.
  assert (H6 : 0 < |1 / x - 0| < δ).
  {
    rewrite Rminus_0_r, Rabs_pos_eq; [| apply Rlt_le, Rdiv_pos_pos; lra]. split.
    - apply Rdiv_pos_pos; lra.
    - apply Rmult_lt_reg_r with (r := x); try lra.
      assert (H6 : (1 / δ) * δ < x * δ) by (apply Rmult_lt_compat_r; lra).
      field_simplify in H6; try lra. field_simplify; lra.
  }
  specialize (H3 (1 / x) H6).
  replace (sin (1 / x) / (1 / x)) with (x * sin (1 / x)) in H3 by (field; lra).
  assert (H7 : x * sin (1 / x) > 1/2) by solve_R.
  assert (H8 : x * (x * sin (1 / x)) > x * (1/2)) by (apply Rmult_lt_compat_l; lra).
  pose proof (Rle_abs M) as H9. solve_R.
Qed.

Lemma lemma_5_39_v : ⟦ lim ∞ ⟧ (λ x, sqrt (x^2 + 2*x) - x) = 1.
Proof.
  intros ε H1. exists (Rmax 1 (1 / ε)). intros x H2.
  assert (H3 : x > 1 /\ x > 1 / ε) by solve_R.
  assert (H4 : ε * x > 1).
  { destruct H3 as [H3 H4]. apply Rmult_lt_compat_r with (r := ε) in H4; auto.
    field_simplify in H4; lra. }
  pose proof (sqrt_pos (x^2 + 2*x)) as H5.
  pose proof (pow2_sqrt (x^2 + 2*x) ltac:(nra)) as H6.
  set (s := sqrt (x^2 + 2*x)) in *.
  assert (H7 : 0 <= s - x <= 1) by nra.
  assert (H8 : (1 - (s - x)) * (s + x) = s - x) by nra.
  rewrite Rabs_left1; nra.
Qed.

Lemma lemma_5_39_vi : ⟦ lim ∞ ⟧ (λ x, x * (sqrt (x + 2) - sqrt x)) = ∞.
Proof.
  intros M. set (K := |M| + 1).
  exists (16 * K^2 + 2). intros x H1.
  assert (H2 : K > 0 /\ M < K) by (unfold K; solve_R).
  assert (H3 : x > 2) by nra.
  pose proof (sqrt_pos (x + 2)) as H4.
  pose proof (sqrt_pos x) as H5.
  pose proof (pow2_sqrt (x + 2) ltac:(lra)) as H6.
  pose proof (pow2_sqrt x ltac:(lra)) as H7.
  set (s := sqrt (x + 2)) in *. set (t := sqrt x) in *.
  assert (H8 : 0 < s - t) by nra.
  assert (H9 : (s - t) * (s + t) = 2) by nra.
  assert (H10 : (s + t)^2 <= 4 * (x + 2)) by nra.
  assert (H11 : K^2 * (s + t)^2 <= K^2 * (4 * (x + 2))) by nra.
  assert (H12 : K * (s + t) < x) by nra.
  assert (H13 : K * (s + t) * (s - t) < x * (s - t)) by (apply Rmult_lt_compat_r; lra).
  nra.
Qed.

Lemma lemma_5_39_vii : ⟦ lim ∞ ⟧ (λ x, sqrt (Rabs x) / x) = 0.
Proof.
  intros ε H1. exists (Rmax 1 (1 / ε^2)). intros x H2.
  assert (H3 : x > 1 /\ x > 1 / ε^2) by solve_R.
  assert (H4 : ε^2 * x > 1).
  { destruct H3 as [H3 H4]. apply Rmult_lt_compat_r with (r := ε^2) in H4; try nra.
    field_simplify in H4; nra. }
  rewrite Rabs_pos_eq with (x := x); try lra.
  pose proof (sqrt_pos x) as H5.
  pose proof (pow2_sqrt x ltac:(lra)) as H6.
  rewrite Rminus_0_r, Rabs_div, Rabs_pos_eq, Rabs_pos_eq; try lra.
  apply Rmult_lt_reg_r with (r := x); try lra.
  field_simplify; try lra.
  assert (H7 : 1 * x < (ε^2 * x) * x) by (apply Rmult_lt_compat_r; lra).
  assert (H8 : 0 < ε * x) by nra. nra.
Qed.
