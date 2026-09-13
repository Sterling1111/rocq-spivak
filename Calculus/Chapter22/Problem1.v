From Calculus.Chapter22 Require Import Prelude.
From Lib Require Import Prime.
Open Scope R_scope.

Lemma lemma_22_1_constant_zero : ⟦ lim ⟧ (λ n, 0) = 0.
Proof.
  intros ε H1. exists 1. intros n H2. solve_R.
Qed.

Lemma lemma_22_1_i : ⟦ lim ⟧ (λ n, n / (n + 1)) = 1.
Proof.
  intros ε H1.
  exists (1 / ε).
  intros n H2.
  apply Rmult_gt_compat_r with (r := ε) in H2; auto.
  field_simplify in H2; try lra.
  apply Rabs_def1;
  apply Rmult_lt_reg_r with (r := (n + 1)); field_simplify; nra.
Qed.

Lemma lemma_22_1_ii : ⟦ lim ⟧ (λ n, (n + 3) / (n ^ 3 + 4)) = 0.
Proof.
  intros ε H1. exists (Rmax 1 (4/ε)). intros n H2.
  assert (H3 : n > 1 /\ n > 4/ε) by solve_R.
  assert (H4 : 4 < ε * n).
  { destruct H3 as [_ H3]. apply Rmult_gt_compat_r with (r := ε) in H3; auto.
    field_simplify in H3; lra. }
  assert (H5 : n ^ 3 + 4 > 0) by nra.
  assert (H6 : n ^ 3 + 4 >= n ^ 2) by nra.
  rewrite Rminus_0_r, Rabs_right.
  - apply (Rmult_lt_reg_r (n ^ 3 + 4)); [lra |].
    field_simplify; nra.
  - apply Rle_ge. left. apply Rdiv_pos_pos; lra.
Qed.

Lemma lemma_22_1_iii :
  ⟦ lim ⟧ (λ n, (n ^ 2 + 1) ^^ (1 / 8) -
                 (n + 1) ^^ (1 / 4)) = 0.
Abort.

Lemma lemma_22_1_iv : ⟦ lim ⟧ (λ n, n! / (n ^ n)) = 0.
Abort.

Lemma lemma_22_1_v : ∀ a, a > 0 -> ⟦ lim ⟧ (λ n, a ^^ (1 / n)) = 1.
Proof.
  intros a H1 ε H2.
  assert (H3 : continuous_at (λ x, a ^^ x) 0) by auto_cont.
  unfold continuous_at in H3. cbn beta in H3.
  rewrite Rpower_0 in H3; [| lra].
  destruct (H3 ε H2) as [δ [H4 H5]].
  destruct (theorem_34_12 δ H4) as [N H6].
  exists (Rmax N 1). intros n H7. apply H5.
  specialize (H6 n ltac:(solve_R)).
  assert (H8 : n > 1) by solve_R.
  split; [rewrite Rminus_0_r; apply Rabs_pos_lt; apply Rgt_not_eq; apply Rdiv_pos_pos; lra | auto].
Qed.

Lemma lemma_22_1_vi : ⟦ lim ⟧ (λ n, n ^^ (1 / n)) = 1.
Abort.

Lemma lemma_22_1_vii : ⟦ lim ⟧ (λ n, (n^2 + n) ^^ (1 / n)) = 1.
Abort.

Lemma lemma_22_1_viii : ∀ a b, a >= 0 -> b >= 0 -> ⟦ lim ⟧ (λ n, (a^n + b^n) ^^ (1 / n)) = Rmax a b.
Abort.

Lemma lemma_22_1_ix : ∀ alpha : ℕ -> ℕ,
  (∀ n, (0 < n)%nat ->
    (card (λ p : ℤ, Z.prime p /\ (p | Z.of_nat n)%Z) = alpha n)%set) ->
  ⟦ lim ⟧ (λ n, alpha n / n) = 0.
Abort.

Lemma lemma_22_1_x : ∀ p : ℕ, ⟦ lim ⟧ (λ n, (∑ 1 n (λ k, k ^ p)) / n ^ (S p)) = 1 / (S p).
Abort.
