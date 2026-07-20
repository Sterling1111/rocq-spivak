From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_34 : ∀ f L,
  ⟦ lim 0⁺ ⟧ (λ x, f (1 / x)) = L <-> ⟦ lim ∞ ⟧ f = L.
Proof.
  intros f L. split.
  - intros H1 N H2.
    specialize (H1 N H2) as [δ [H3 H4]].
    exists (1 / δ).
    intros x H5.
    specialize (H4 (1 / x)).
    rewrite Rminus_0_r in H4.
    repeat rewrite Rdiv_1_l in H4.
    rewrite Rinv_inv in H4.
    apply H4.
    assert (H6 : 0 < x).
    {
      apply Rmult_gt_compat_r with (r := δ) in H5; auto.
      field_simplify in H5; solve_R.
    }
    split.
    + apply Rinv_pos; auto.
    + apply Rmult_lt_reg_r with (r := x); auto.
      apply Rmult_lt_compat_r with (r := δ) in H5; [| solve_R].
      field_simplify in H5; [| solve_R].
      field_simplify; solve_R.
  - intros H1 ε H2.
    specialize (H1 ε H2) as [N H1].
    exists (1 / (|N| + 1)); split.
    + apply Rdiv_pos_pos; solve_R.
    + intros x [H3 H4].
      rewrite Rminus_0_r in *.
      apply H1.
      apply Rmult_gt_reg_r with (r := x); auto.
      apply Rmult_lt_compat_r with (r := (|N| + 1)) in H4; [ | solve_R].
      field_simplify in H4; [ | solve_R].
      field_simplify; solve_R.
Qed.