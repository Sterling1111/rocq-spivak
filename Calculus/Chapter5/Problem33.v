From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_33_i : ⟦ lim ∞ ⟧ (λ x, (x + (sin x)^3) / (5 * x + 6)) = 1/5.
Proof.
  intros ε H1. exists (Rmax 1 (1 / ε)). intros x H2.
  assert (H3 : x > 1 /\ x > 1 / ε) by solve_R.
  assert (H4 : ε * x > 1).
  { destruct H3 as [H3 H4]. apply Rmult_lt_compat_r with (r := ε) in H4; auto.
    field_simplify in H4; lra. }
  pose proof (sin_bounds x) as H5.
  assert (H6 : -1 <= (sin x)^3 <= 1) by solve_R.
  replace ((x + (sin x)^3) / (5*x + 6) - 1/5) with
    ((5 * (sin x)^3 - 6) / (5 * (5*x + 6))) by (field; lra).
  rewrite Rabs_div, Rabs_left, Rabs_pos_eq; try nra.
  apply Rmult_lt_reg_r with (r := 5 * (5*x + 6)); try nra.
  field_simplify; nra.
Qed.

Lemma lemma_5_33_ii : ⟦ lim ∞ ⟧ (λ x, x * sin x / (x^2 + 5)) = 0.
Proof.
  intros ε H1. exists (Rmax 1 (1 / ε)). intros x H2.
  assert (H3 : x > 1 /\ x > 1 / ε) by solve_R.
  assert (H4 : ε * x > 1).
  { destruct H3 as [H3 H4]. apply Rmult_lt_compat_r with (r := ε) in H4; auto.
    field_simplify in H4; lra. }
  pose proof (sin_bounds x) as H5.
  rewrite Rminus_0_r, Rabs_div, Rabs_mult.
  rewrite Rabs_pos_eq with (x := x); try lra.
  rewrite Rabs_pos_eq with (x := x^2 + 5); try nra.
  apply Rmult_lt_reg_r with (r := x^2 + 5); try nra.
  field_simplify; try nra. assert (H6 : |sin x| <= 1) by solve_R. nra.
Qed.

Lemma lemma_5_33_iii : ⟦ lim ∞ ⟧ (λ x, sqrt (x^2 + x) - x) = 1/2.
Proof.
  intros ε H1. exists (Rmax 1 (1 / ε)). intros x H2.
  assert (H3 : x > 1 /\ x > 1 / ε) by solve_R.
  assert (H4 : ε * x > 1).
  { destruct H3 as [H3 H4]. apply Rmult_lt_compat_r with (r := ε) in H4; auto.
    field_simplify in H4; lra. }
  pose proof (sqrt_pos (x^2 + x)) as H5.
  pose proof (pow2_sqrt (x^2 + x) ltac:(nra)) as H6.
  set (s := sqrt (x^2 + x)) in *.
  assert (H7 : 0 <= s - x <= 1/2) by nra.
  assert (H8 : (1/2 - (s - x)) * (s + x) = (s - x)/2) by nra.
  rewrite Rabs_left1; nra.
Qed.

Lemma lemma_5_33_iv : ¬ ∃ L, ⟦ lim ∞ ⟧ (λ x, x^2 * (1 + (sin x)^2) / (x + sin x)^2) = L.
Proof.
  intros [L H1]. specialize (H1 (1/10) ltac:(lra)) as [N H2].
  destruct (INR_unbounded (Rmax N 10 / π)) as [n H3].
  pose proof π_pos as H4.
  assert (H5 : n * π > Rmax N 10).
  { apply Rmult_lt_compat_r with (r := π) in H3; auto. field_simplify in H3; lra. }
  specialize (H2 (n * π) ltac:(solve_R)) as H6.
  rewrite sin_n_pi in H6.
  replace ((n * π)^2 * (1 + 0^2) / (n * π + 0)^2) with 1 in H6 by (field; solve_R).
  set (y := n * π + π/2).
  specialize (H2 y ltac:(unfold y; solve_R)) as H7.
  assert (H8 : (sin y)^2 = 1).
  { unfold y. rewrite sin_plus, sin_π_over_2, cos_π_over_2, sin_n_pi.
    pose proof (pythagorean_identity (n * π)) as H8. rewrite sin_n_pi in H8. nra. }
  assert (H9 : y > 10) by (unfold y; solve_R).
  pose proof (sin_bounds y) as H10.
  assert (H11 : (y + sin y)^2 > 0) by nra.
  assert (H12 : y^2 * (1 + (sin y)^2) / (y + sin y)^2 > 3/2).
  {
    apply Rmult_lt_reg_r with (r := (y + sin y)^2); auto.
    field_simplify; nra.
  }
  solve_R.
Qed.
