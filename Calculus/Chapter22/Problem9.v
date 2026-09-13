From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_9_i :
  ⟦ lim ⟧ (λ n, (∑ 1 n (λ k, exp (k / n))) / n) = exp 1 - 1.
Abort.

Lemma lemma_22_9_ii :
  ⟦ lim ⟧ (λ n, (∑ 1 (2 * n) (λ k, exp (k / n))) / n) = exp 2 - 1.
Abort.

Lemma lemma_22_9_iii :
  ⟦ lim ⟧ (λ n, ∑ 1 n (λ k, 1 / (n + k)%nat)) = log 2.
Abort.

Lemma lemma_22_9_iv :
  ⟦ lim ⟧ (λ n, ∑ 0 n (λ k, 1 / ((n + k) ^ 2)%nat)) = 0.
Proof.
  intros ε H1. exists (Rmax 1 (2/ε)). intros n H2.
  assert (H3 : n > 1 /\ n > 2/ε) by solve_R.
  assert (H4 : 2 < ε*n).
  { destruct H3 as [_ H3]. apply Rmult_gt_compat_r with (r := ε) in H3; auto.
    field_simplify in H3; lra. }
  assert (H5 : ∀ k, (0 <= k <= n)%nat ->
    0 <= 1/((n+k)%nat^2)%nat <= 1/n^2).
  { intros k H5. rewrite pow_INR, plus_INR. pose proof (pos_INR k). split.
    - left. apply Rdiv_pos_pos; nra.
    - unfold Rdiv. rewrite !Rmult_1_l. apply Rinv_le_contravar; nra. }
  assert (H6 : 0 <= ∑ 0 n (λ k, 1/((n+k)%nat^2)%nat)).
  { apply sum_f_nonneg; [lia |]. intros k H6. apply H5. auto. }
  assert (H7 : (∑ 0 n (λ k, 1/((n+k)%nat^2)%nat)) <=
    (n+1)/n^2).
  { pose proof (sum_f_le (λ k, 1/((n+k)%nat^2)%nat) 0 n (1/n^2)) as H7.
    specialize (H7 ltac:(lia) ltac:(intros k H8; apply H5; auto)).
    rewrite Nat.sub_0_r, plus_INR in H7. simpl INR in H7.
    replace ((n+1)/n^2) with ((1/n^2)*(n+1))
      by (unfold Rdiv; ring). exact H7. }
  rewrite Rminus_0_r, Rabs_right; [| lra].
  apply Rle_lt_trans with (r2 := (n+1)/n^2); [auto |].
  apply (Rmult_lt_reg_r (n^2)); [nra |]. field_simplify; nra.
Qed.

Lemma lemma_22_9_v :
  ⟦ lim ⟧ (λ n, ∑ 1 n (λ k, n / ((n + k) ^ 2)%nat)) = 1 / 2.
Abort.

Lemma lemma_22_9_vi :
  ⟦ lim ⟧ (λ n, ∑ 1 n (λ k, n / (n^2 + k^2)%nat)) = π / 4.
Abort.
