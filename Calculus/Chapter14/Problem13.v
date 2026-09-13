From Calculus.Chapter14 Require Import Prelude.
From Lib Require Import Exponential.

Lemma lemma_14_13 : ∀ (n : nat) b,
  (n > 0)%nat ->
  b > 0 ->
  ∫ 0 b (λ x, x ^^ (1 / n)) = b ^^ (1 / n + 1) / (1 / n + 1).
Proof.
  intros n b H1 H2.
  assert (H3 : 0 < 1 / n) by (apply Rdiv_pos_pos; [lra | apply lt_0_INR; lia]).
  assert (H4 : ∀ p, p > 0 -> continuous_on (λ x, x ^^ p) [0, b]).
  {
    intros p H4 x H5. destruct (Req_dec x 0) as [H6 | H6].
    - subst. rewrite Rpower_0_base; [| lra].
      intros ε H6.
      destruct (limit_Rabs_Rpower_zero p H4 ε H6) as [δ [H7 H8]].
      exists δ. split; [lra |]. intros y H9 H10.
      specialize (H8 y H10).
      replace (|y|) with y in H8 by (symmetry; apply Rabs_right; solve_R).
      exact H8.
    - apply limit_imp_limit_on.
      apply continuous_at_Rpower_const. solve_R.
  }
  replace (b ^^ (1 / n + 1) / (1 / n + 1)) with
    ((λ x, x ^^ (1 / n + 1) / (1 / n + 1)) b -
     (λ x, x ^^ (1 / n + 1) / (1 / n + 1)) 0)
    by (cbn beta; rewrite Rpower_0_base; [lra | lra]).
  apply FTC2_open with (g := λ x, x ^^ (1 / n + 1) / (1 / n + 1)).
  - lra.
  - apply H4. lra.
  - apply continuous_on_div; [intros x H5; lra | apply H4; lra | auto_cont].
  - auto_diff.
Qed.
