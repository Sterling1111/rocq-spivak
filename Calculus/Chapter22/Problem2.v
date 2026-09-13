From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_2_i : ⟦ lim ⟧ (λ n, n / (n + 1)%nat - (n + 1)%nat / n) = 0.
Proof.
  intros ε H1. exists (Rmax 1 (3/ε)). intros n H2.
  rewrite plus_INR. simpl INR.
  assert (H3 : n > 1 /\ n > 3/ε) by solve_R.
  assert (H4 : 3 < ε*n).
  { destruct H3 as [_ H3]. apply Rmult_gt_compat_r with (r := ε) in H3; auto.
    field_simplify in H3; lra. }
  replace (n/(n+1)-(n+1)/n-0)
    with (- ((2*n+1)/(n*(n+1)))) by (field; lra).
  rewrite Rabs_Ropp, Rabs_right.
  - apply (Rmult_lt_reg_r (n*(n+1))); [nra |].
    field_simplify; nra.
  - left. apply Rdiv_pos_pos; nra.
Qed.

Lemma lemma_22_2_ii : ∀ a b,
  ⟦ lim ⟧ (λ n, n - √ (n + a) * √ (n + b)) = - (a + b) / 2.
Abort.

Lemma lemma_22_2_iii : ⟦ lim ⟧ (λ n, (2^n + (-1)^n) / (2^(n+1) + (-1)^(n+1))) = 1 / 2.
Proof.
  intros ε H1.
  destruct (pow_lt_1_zero (1/2) ltac:(solve_R) (ε/3) ltac:(lra)) as [N H2].
  exists (Rmax 1 (N : ℝ)). intros n H3.
  assert (H4 : (0 < n)%nat /\ (N <= n)%nat).
  { assert (H4 : n > 1 /\ n > N) by solve_R.
    destruct H4 as [H4 H5]. change (1%nat < n) in H4. apply INR_lt in H4. apply INR_lt in H5. lia. }
  assert (H5 : 2 <= 2^n).
  { assert (H5 : ∀ k, 1 <= 2^k).
    { intros k. induction k; simpl; nra. }
    destruct n; [lia | simpl; pose proof (H5 n); nra]. }
  pose proof (H2 n ltac:(lia)) as H6.
  rewrite Rabs_right in H6; [| left; apply pow_lt; lra].
  assert (H7 : (1/2)^n * 2^n = 1).
  { rewrite <- Rpow_mult_distr. replace (1/2*2) with 1 by field. apply pow1. }
  assert (H8 : 3 < ε*2^n) by nra.
  replace (n+1)%nat with (S n) by lia. simpl pow.
  destruct (pow_neg1_n n) as [H9 | H9]; rewrite H9.
  - replace ((2^n+1)/(2*2^n + -1*1)-1/2)
      with (3/(2*(2*2^n-1))) by (field; nra).
    apply Rabs_def1; apply (Rmult_lt_reg_r (2*(2*2^n-1))); try nra;
      field_simplify; nra.
  - replace ((2^n + -1)/(2*2^n + -1* -1)-1/2)
      with (-3/(2*(2*2^n+1))) by (field; nra).
    apply Rabs_def1; apply (Rmult_lt_reg_r (2*(2*2^n+1))); try nra;
      field_simplify; nra.
Qed.

Lemma lemma_22_2_iv : ⟦ lim ⟧ (λ n, (-1)^n * √ n * sin (n ^ n) / (n + 1)%nat) = 0.
Proof.
  intros ε H1. exists (Rmax 1 (1/ε^2)). intros n H2.
  assert (H3 : n > 1 /\ n > 1/ε^2) by solve_R.
  assert (H4 : 1 < ε^2*n).
  { destruct H3 as [_ H3]. apply Rmult_gt_compat_r with (r := ε^2) in H3; [| nra].
    field_simplify in H3; nra. }
  pose proof (sqrt_pos (n : ℝ)) as H5.
  assert (H6 : sqrt (n)*sqrt (n : ℝ) = (n : ℝ)) by (apply sqrt_sqrt; lra).
  assert (H7 : 1 < ε*sqrt (n : ℝ)).
  { rewrite <- H6 in H4.
    assert (H7 : 0 <= ε*sqrt (n : ℝ)) by nra.
    nra. }
  assert (H8 : sqrt (n) < ε*(n+1)).
  { pose proof (Rmult_lt_compat_r (sqrt (n : ℝ)) 1 (ε*sqrt (n : ℝ)) ltac:(nra) H7).
    nra. }
  rewrite Rminus_0_r, Rabs_div, plus_INR. simpl INR.
  rewrite (Rabs_right (n+1) ltac:(lra)).
  apply (Rmult_lt_reg_r (n+1)); [lra |]. field_simplify; [| lra].
  repeat rewrite Rabs_mult. rewrite (Rabs_right (sqrt (n : ℝ)) ltac:(lra)).
  destruct (pow_neg1_n n) as [H9 | H9]; rewrite H9;
    pose proof (sin_bounds (n ^ n)); solve_R.
Qed.

Lemma lemma_22_2_v : ∀ a b, a + b <> 0 ->
  ⟦ lim ⟧ (λ n, (a^n - b^n) / (a^n + b^n)) =
    (if Rlt_dec (|a|) (|b|) then -1
     else if Rlt_dec (|b|) (|a|) then 1 else 0).
Abort.

Lemma lemma_22_2_vi : ∀ c, |c| < 1 ->
  ⟦ lim ⟧ (λ n, n * c^n) = 0.
Abort.

Lemma lemma_22_2_vii :
  ⟦ lim ⟧ (λ n, 2^(n^2) / n!) = ∞.
Abort.
