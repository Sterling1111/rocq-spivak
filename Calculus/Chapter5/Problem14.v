From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_14_a : ∀ (f : R -> R) (l b : R),
  ⟦ lim 0 ⟧ (λ x, f x / x) = l -> b <> 0 ->
  ⟦ lim 0 ⟧ (λ x, f (b * x) / x) = b * l.
Proof.
  intros f l b H1 H2.
  apply limit_eq with (f1 := λ x : ℝ, b * (f (b * x) / (b * x))).
  { exists 1; split; solve_R. }
  apply limit_mult_const_l.
  intros ε H3.
  specialize (H1 ε H3) as [δ [H4 H5]].
  exists (δ / |b|); split.
  - apply Rmult_gt_reg_r with (r := |b|); field_simplify; solve_R.
  - intros x [H6 H7].
    specialize (H5 (b * x)). 
    rewrite Rminus_0_r in *.
    assert (|(b * x)| < δ) as H8.
    { apply Rmult_lt_compat_r with (r := |b|) in H7; field_simplify in H7; solve_R. }
    specialize (H5 ltac:(solve_R)).
    auto.
Qed.

Lemma lemma_5_14_b :
  ∀ (f : R -> R),
    (∃ l, ⟦ lim 0 ⟧ (λ x, f (0 * x) / x) = l) <-> f 0 = 0.
Proof.
  intros f; split.
  - intros [l H1].
    replace (λ x, f (0 * x) / x) with (λ x, f 0 / x) in H1.
    2 : { extensionality x. rewrite Rmult_0_l. reflexivity. }
    destruct (Req_dec (f 0) 0) as [H2|H2]; auto.
    exfalso.
    specialize (H1 1 ltac:(solve_R)) as [δ [H1 H3]].
    set (x := Rmin (δ / 2) (|f 0| / (2 * (|l| + 1)))).
    assert (H4 : x > 0). 
    {
      unfold x. apply Rmin_pos.
      - lra.
      - apply Rmult_lt_reg_r with (r := (2 * (|l| + 1))); field_simplify; solve_R.
    }
    assert (H5 : 0 < |x - 0| < δ) by (unfold x in *; solve_R).

    specialize (H3 x H5). 

    assert (H6 : |f 0 / x| >= 2 * (|l| + 1)).
    {
      rewrite Rabs_div. rewrite Rabs_pos_eq with (x := x); try lra.
      assert (H6 : x <= |f 0| / (2 * (|l| + 1))) by (unfold x; apply Rmin_r).
      apply Rle_ge.
      apply Rmult_le_reg_r with (r := x); [solve_R |].
      replace (|f 0| / x * x) with (|f 0|) by solve_R.
      apply Rmult_le_compat_r with (r := (2 * (|l| + 1))) in H6; [| solve_R].
      field_simplify in H6; solve_R.
    }
    solve_R.
  - intros H1.
    exists 0.
    apply limit_eq with (f1 := λ x, 0).
    2 : { exists 1. split; solve_R. }
    exists 1; split; try lra.
    intros x H2.
    rewrite Rmult_0_l.
    solve_R.
Qed.