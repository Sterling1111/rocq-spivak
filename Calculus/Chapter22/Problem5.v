From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_5_a : ∀ a,
  0 < a < 2 -> a < √ (2 * a) < 2.
Proof.
  intros a H1. solve_R.
Qed.

Lemma lemma_22_5_b : ∀ a : sequence,
  a 0%nat = √ 2 -> (∀ n, a (S n) = √ (2 * a n)) ->
  convergent_sequence a.
Proof.
  intros a H1 H2.
  assert (H3 : ∀ n, 0 < a n < 2).
  { intros n. induction n as [| n IH].
    - rewrite H1. solve_R.
    - rewrite H2. pose proof (lemma_22_5_a (a n) IH). lra. }
  apply monotone_convergence_nondecreasing.
  - intros n. rewrite H2. pose proof (lemma_22_5_a (a n) (H3 n)). lra.
  - exists 2. intros n. specialize (H3 n). lra.
Qed.

Lemma lemma_22_5_c : ∀ a : sequence,
  a 0%nat = √ 2 -> (∀ n, a (S n) = √ (2 * a n)) ->
  ⟦ lim ⟧ a = 2.
Proof.
  intros a H1 H2. destruct (lemma_22_5_b a H1 H2) as [L H3].
  assert (H4 : ∀ n, √ 2 <= a n).
  { intros n. induction n as [| n IH]; [rewrite H1; lra |].
    rewrite H2. assert (H4 : 0 < a n < 2).
    { clear IH. induction n as [| n IH]; [rewrite H1; solve_R |].
      rewrite H2. pose proof (lemma_22_5_a (a n) IH). lra. }
    pose proof (lemma_22_5_a (a n) H4). lra. }
  assert (H5 : √ 2 <= L).
  { apply Rnot_lt_le. intros H5.
    destruct (H3 (√ 2-L) ltac:(lra)) as [N H6].
    destruct (INR_unbounded N) as [n H7].
    specialize (H6 n H7). specialize (H4 n). solve_R. }
  assert (H6 : L = √ (2*L)).
  { apply limit_of_sequence_unique with (a := λ n, a (S n)).
    - intros ε H6. destruct (H3 ε H6) as [N H7].
      exists N. intros n H8. apply H7. rewrite S_INR. lra.
    - assert (H6 : continuous (λ x, √ (2*x))) by auto_cont.
      intros ε H7. destruct (H6 L ε H7) as [δ [H8 H9]].
      destruct (H3 δ H8) as [N H10]. exists N. intros n H11. rewrite H2.
      destruct (Req_dec (a n) L) as [H12 | H12].
      + rewrite H12. solve_R.
      + apply H9. specialize (H10 n H11). solve_R. }
  assert (H7 : 0 <= 2*L) by (pose proof (sqrt_pos 2); lra).
  pose proof (sqrt_sqrt (2*L) H7) as H8.
  rewrite <- H6 in H8.
  assert (H9 : 0 < L).
  { pose proof (sqrt_lt_R0 2 ltac:(lra)). lra. }
  assert (H10 : L = 2) by nra.
  subst L. auto.
Qed.
