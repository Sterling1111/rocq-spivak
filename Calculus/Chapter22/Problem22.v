From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_22_a : ∀ c m n,
  c <> 1 -> (m <= n)%nat ->
  ∑ m n (λ i, c ^ i) = (c ^ m - c ^ (n + 1)) / (1 - c).
Proof.
  intros c m n H1 H2. induction n as [| n IH].
  - assert (m = 0%nat) by lia. subst m. rewrite sum_f_0_0. simpl. field. lra.
  - destruct (Nat.eq_dec m (S n)) as [H3 | H3].
    + subst m. rewrite sum_f_n_n. replace (S n + 1)%nat with (S (S n)) by lia.
      simpl pow. field. lra.
    + rewrite sum_f_i_Sn_f, IH; try lia.
      replace (n+1)%nat with (S n) by lia.
      replace (S n+1)%nat with (S (S n)) by lia.
      simpl pow. field. lra.
Qed.

Lemma lemma_22_22_b : ∀ c,
  |c| < 1 ->
  ∀ ε, ε > 0 ->
  ∃ N, ∀ m n, (n >= m)%nat -> (m >= N)%nat ->
  |∑ m n (λ i, c ^ i)| < ε.
Proof.
  intros c H1 ε H2.
  assert (H3 : 0 < 1-c) by solve_R.
  destruct (pow_lt_1_zero c H1 (ε*(1-c)/2) ltac:(nra)) as [N H4].
  exists N. intros m n H5 H6. rewrite lemma_22_22_a; try lia; try lra.
  rewrite Rabs_div, (Rabs_right (1-c) ltac:(lra)).
  apply (Rmult_lt_reg_r (1-c)); [lra |].
  field_simplify; [| lra].
  pose proof (Rabs_triang (c^m) (-(c^(n+1)))) as H7.
  rewrite Rabs_Ropp in H7.
  pose proof (H4 m H6) as H8. pose proof (H4 (n+1)%nat ltac:(lia)) as H9.
  unfold Rminus in *. nra.
Qed.

Lemma lemma_22_22_c : ∀ x c,
  0 < c < 1 ->
  (∀ n, |x (n + 1)%nat - x n| <= c ^ n) ->
  cauchy_sequence x.
Proof.
  intros x c H1 H2.
  assert (H3 : ∀ m n, (m <= n)%nat ->
    Rabs (x (S n) - x m) <= ∑ m n (λ k, c^k)).
  {
    intros m n H3. induction n as [| n IH].
    - assert (m = 0%nat) by lia. subst m. rewrite sum_f_0_0.
      specialize (H2 0%nat). exact H2.
    - destruct (Nat.eq_dec m (S n)) as [H4 | H4].
      + subst m. rewrite sum_f_n_n. replace (S (S n)) with (S n+1)%nat by lia. auto.
      + rewrite sum_f_i_Sn_f; [| lia].
        specialize (IH ltac:(lia)). specialize (H2 (S n)).
        replace (S n+1)%nat with (S (S n)) in H2 by lia.
        pose proof (Rabs_triang (x (S (S n))-x (S n)) (x (S n)-x m)) as H5.
        replace (x (S (S n))-x (S n)+(x (S n)-x m))
          with (x (S (S n))-x m) in H5 by ring. lra.
  }
  intros ε H4. destruct (lemma_22_22_b c ltac:(solve_R) ε H4) as [N H5].
  assert (H6 : ∀ m n, (N <= m)%nat -> (m < n)%nat -> Rabs (x n-x m) < ε).
  { intros m n H6 H7. destruct n as [| n]; [lia |].
    specialize (H3 m n ltac:(lia)). specialize (H5 m n ltac:(lia) H6).
    pose proof (Rle_abs (∑ m n (λ k, c^k))). lra. }
  exists (N : ℝ). intros n m H7 H8.
  apply INR_lt in H7. apply INR_lt in H8.
  destruct (Nat.lt_trichotomy n m) as [H9 | [H9 | H9]].
  - rewrite Rabs_minus_sym. apply H6; lia.
  - subst m. solve_R.
  - apply H6; lia.
Qed.
