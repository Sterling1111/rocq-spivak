From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_12_a : ∀ n : ℕ,
  (n > 0)%nat ->
  1 / (n + 1)%nat < log ((n + 1)%nat) - log n < 1 / n.
Proof.
  intros n H1.
  assert (H2 : 0 < n) by (apply lt_0_INR; lia).
  assert (H3 : ((n+1)%nat : ℝ) = n+1) by (rewrite plus_INR; simpl; lra).
  pose proof (integral_bounds_strong_open (n : ℝ) (((n+1)%nat : ℝ))
    (λ x, 1/x) (1/(n+1)%nat) (1/n)) as H4.
  assert (H5 : 1/(n+1)%nat < ∫ (n : ℝ) (((n+1)%nat : ℝ)) (λ x, 1/x) < 1/n).
  { specialize (H4 ltac:(lra) ltac:(intros x H5; rewrite H3 in *; solve_R)
      ltac:(auto_cont; rewrite H3 in *; solve_R)).
    rewrite H3 in H4. replace (n+1-n) with 1 in H4 by ring. rewrite H3. lra. }
  rewrite (FTC2 (n : ℝ) (((n+1)%nat : ℝ)) (λ x, 1/x) log) in H5.
  - auto.
  - lra.
  - auto_cont.
  - apply derivative_log_on; lra.
Qed.

Lemma lemma_22_12_b : ∀ a,
  (∀ n, a n = ∑ 1 (S n) (λ k, 1 / k) - log (S n)) ->
  decreasing a /\ (∀ n, a n >= 0) /\ convergent_sequence a.
Proof.
  intros a H1.
  assert (H2 : decreasing a).
  { intros n. rewrite (H1 n), (H1 (S n)), (sum_f_i_Sn_f _ 1 (S n)); [| lia].
    pose proof (lemma_22_12_a (S n) ltac:(lia)) as H2.
    replace (S n+1)%nat with (S (S n)) in H2 by lia. lra. }
  assert (H3 : ∀ n, a n >= 0).
  { intros n. induction n as [| n IH].
    - rewrite H1, sum_f_n_n. simpl. rewrite log_1. lra.
    - assert (H3 : log ((S (S n))%nat) < ∑ 1 (S n) (λ (k : ℕ), 1/k)).
      { clear IH H2. induction n as [| n IH].
        - rewrite sum_f_n_n. pose proof (lemma_22_12_a 1 ltac:(lia)) as H2.
          cbn [INR Nat.add] in H2. rewrite log_1 in H2. simpl in *. lra.
        - rewrite sum_f_i_Sn_f; [| lia].
          pose proof (lemma_22_12_a (S (S n)) ltac:(lia)) as H2.
          replace (S (S n)+1)%nat with (S (S (S n))) in H2 by lia. lra. }
      rewrite H1, sum_f_i_Sn_f; [| lia].
      assert (H4 : 0 < 1/(S (S n))%nat) by (apply Rdiv_pos_pos; solve_R). lra. }
  split; auto. split; auto. apply monotone_convergence_nonincreasing.
  - intros n. specialize (H2 n). lra.
  - exists 0. intros n. specialize (H3 n). lra.
Qed.
