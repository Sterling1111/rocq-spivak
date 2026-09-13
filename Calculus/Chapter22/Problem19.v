From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_19_a : ∀ a L,
  (∀ n, 0 <= a n <= 1) ->
  ⟦ lim ⟧ a = L ->
  0 <= L <= 1.
Proof.
  intros a L H1 H2.
  split; apply Rnot_lt_le; intros H3.
  - destruct (H2 (-L) ltac:(lra)) as [N H4].
    destruct (INR_unbounded N) as [n H5].
    specialize (H4 n H5). specialize (H1 n). solve_R.
  - destruct (H2 (L-1) ltac:(lra)) as [N H4].
    destruct (INR_unbounded N) as [n H5].
    specialize (H4 n H5). specialize (H1 n). solve_R.
Qed.

Lemma lemma_22_19_b : ∃ a L,
  (∀ n, 0 < a n < 1) /\ ⟦ lim ⟧ a = L /\ ~ (0 < L < 1).
Proof.
  exists (λ n, 1 / (n + 2)), 0. split.
  - intros n. pose proof (pos_INR n). solve_R.
  - split; [| lra]. intros ε H1. exists (1/ε). intros n H2.
    pose proof (pos_INR n).
    assert (H3 : 1 < ε * n).
    { apply Rmult_gt_compat_r with (r := ε) in H2; auto.
      field_simplify in H2; lra. }
    apply Rabs_def1;
      apply (Rmult_lt_reg_r (n + 2)); try lra;
      field_simplify; nra.
Qed.
