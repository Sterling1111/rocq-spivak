From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_29_a : ∀ (a : ℝ) (x y : ℚ),
  0 < a -> x < y ->
  (1 < a -> a ^^ x < a ^^ y) /\
  (a < 1 -> a ^^ x > a ^^ y).
Proof.
  intros a x y H1 H2. repeat rewrite Rpower_def_pos; try lra.
  split; intros H3.
  - assert (H4 : 0 < log a).
    { pose proof (log_increasing 1 a ltac:(solve_R) ltac:(solve_R) H3).
      rewrite log_1 in H. lra. }
    apply exp_increasing; solve_R.
  - assert (H4 : log a < 0).
    { pose proof (log_increasing a 1 ltac:(solve_R) ltac:(solve_R) H3).
      rewrite log_1 in H. lra. }
    apply exp_increasing; solve_R.
Qed.

Lemma lemma_22_29_b : ∀ a ε,
  0 < a -> ε > 0 ->
  ∃ δ, δ > 0 /\ ∀ x : ℚ,
    |x| < δ -> |a ^^ x - 1| < ε.
Proof.
  intros a ε H1 H2.
  assert (H3 : continuous_at (λ x, a ^^ x) 0) by auto_cont.
  unfold continuous_at in H3. cbn beta in H3.
  rewrite Rpower_0 in H3; [| lra].
  destruct (H3 ε H2) as [δ [H4 H5]]. exists δ. split; auto.
  intros x H6. destruct (Req_dec (x) 0) as [H7 | H7].
  - rewrite H7, Rpower_0; solve_R.
  - apply H5. solve_R.
Qed.

Lemma lemma_22_29_c : ∀ a u v,
  0 < a -> u <= v ->
  uniformly_continuous_on (λ x, a ^^ x)
    (λ x, x ∈ [u, v] /\ rational x).
Proof.
  intros a u v H1 H2.
  assert (H3 : uniformly_continuous_on (λ x, a ^^ x) [u,v]).
  { apply continuous_on_imp_uniformly_continuous_on; auto. auto_cont. }
  intros ε H4. destruct (H3 ε H4) as [δ [H5 H6]].
  exists δ. split; auto. intros x y [H7 H8] [H9 H10] H11. auto.
Qed.

Lemma lemma_22_29_d : ∀ a,
  0 < a -> ∃ f : ℝ -> ℝ,
    (∀ x : ℚ, f x = a ^^ x) /\ continuous f /\
    (1 < a -> Derivative.increasing f) /\
    (a < 1 -> Derivative.decreasing f) /\
    (∀ x y, f (x + y) = f x * f y).
Proof.
  intros a H1. exists (λ x, a ^^ x). split; [auto |].
  split; [auto_cont |]. split.
  - intros H2 x y _ _ H3. repeat rewrite Rpower_def_pos; try lra.
    assert (H4 : 0 < log a).
    { pose proof (log_increasing 1 a ltac:(solve_R) ltac:(solve_R) H2).
      rewrite log_1 in H. lra. }
    apply exp_increasing; solve_R.
  - split.
    + intros H2 x y _ _ H3. repeat rewrite Rpower_def_pos; try lra.
      assert (H4 : log a < 0).
      { pose proof (log_increasing a 1 ltac:(solve_R) ltac:(solve_R) H2).
        rewrite log_1 in H. lra. }
      apply exp_increasing; solve_R.
    + intros x y. apply Rpower_plus. lra.
Qed.
