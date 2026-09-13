From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_10_a : ∀ a,
  a > 1 -> ⟦ lim ⟧ (λ n, a ^ n) = ∞.
Proof.
  intros a H1 M. exists ((M-1)/(a-1)). intros n H2.
  pose proof (bernoulli_inequality n (a-1) ltac:(lra)) as H3.
  replace (1+(a-1)) with a in H3 by ring.
  assert (H4 : M-1 < n * (a-1)).
  { apply (Rmult_lt_reg_r (/ (a-1))); [apply Rinv_0_lt_compat; lra |].
    field_simplify; nra. }
  nra.
Qed.

Lemma lemma_22_10_b : ∀ a,
  0 < a < 1 -> ⟦ lim ⟧ (λ n, a ^ n) = 0.
Proof.
  intros a H1 ε H2.
  destruct (pow_lt_1_zero a ltac:(solve_R) ε H2) as [N H3].
  exists N. intros n H4. rewrite Rminus_0_r. apply H3.
  apply INR_lt in H4. lia.
Qed.

Lemma lemma_22_10_c : ∀ a,
  a > 1 -> ⟦ lim ⟧ (λ n, a ^^ (1 / n)) = 1.
Proof.
  intros a H1 ε H2. exists (Rmax 1 ((a-1)/ε)). intros n H3.
  assert (H4 : n > 1 /\ n > (a-1)/ε) by solve_R.
  assert (H5 : a-1 < ε*n).
  { destruct H4 as [_ H4]. apply Rmult_gt_compat_r with (r := ε) in H4; auto.
    field_simplify in H4; lra. }
  set (y := a ^^ (1/n)).
  assert (H6 : y >= 1).
  { unfold y. apply Rpower_ge_1; [lra | left; apply Rdiv_pos_pos; lra]. }
  assert (H7 : y^n = a).
  { unfold y. rewrite Rpower_pow; try lra.
    replace (n * (1/n)) with 1 by (field; lra).
    apply Rpower_1. lra. }
  pose proof (bernoulli_inequality n (y-1) ltac:(lra)) as H8.
  replace (1+(y-1)) with y in H8 by ring. rewrite H7 in H8.
  change (Rabs (y-1) < ε). rewrite Rabs_right; nra.
Qed.

Lemma lemma_22_10_d : ∀ a,
  0 < a < 1 -> ⟦ lim ⟧ (λ n, a ^^ (1 / n)) = 1.
Proof.
  intros a H1.
  assert (H2 : 1/a > 1) by solve_R.
  pose proof (lemma_22_10_c (1/a) H2) as H3.
  intros ε H4. destruct (H3 ε H4) as [N H5].
  exists (Rmax N 1). intros n H6.
  specialize (H5 n ltac:(solve_R)).
  set (y := (1/a) ^^ (1/n)).
  assert (H7 : y >= 1).
  { unfold y. apply Rpower_ge_1; [lra | left; apply Rdiv_pos_pos; solve_R]. }
  assert (H8 : a ^^ (1/n) * y = 1).
  { unfold y. rewrite <- Rpower_mult_distr; try lra; try (apply Rdiv_pos_pos; lra).
    replace (a*(1/a)) with 1 by (field; lra). apply Rpower_1_base. }
  change (Rabs (y-1) < ε) in H5.
  assert (H9 : 0 < a ^^ (1/n)) by (apply Rpower_gt_0; lra).
  apply Rabs_def1; solve_R; nra.
Qed.

Lemma lemma_22_10_e : ⟦ lim ⟧ (λ n, n ^^ (1 / n)) = 1.
Abort.
