From Calculus.Chapter14 Require Import Prelude.
From Calculus.Chapter13 Require Import Problem23.
Require Import Interval.Tactic.

Lemma lemma_14_7_i :
  1 / (7 * √2) <= ∫ 0 1 (fun x => x^6 / √(1 + x^2)) <= 1 / 7.
Proof.
  set (f := λ x, 1 / √(1 + x ^ 2)).
  set (g := λ x, x^6).

  assert (H1 : 0 < 1) by lra.
  assert (H2 : continuous_on f [0, 1]) by (unfold f; auto_cont).
  assert (H3 : integrable_on 0 1 g) by (apply theorem_13_3; unfold g; auto_cont).
  assert (H4 : nonnegative_on g [0, 1]) by (intros x H4; unfold g; nra).

  pose proof lemma_13_23_d f g 0 1 H1 H2 H3 H4 as [ξ [H5 H6]].

  replace (∫ 0 1 g) with (1/7) in H6 by (unfold g; symmetry; auto_int).

  replace (f ⋅ g) with ((λ x : ℝ, x ^ 6 / √(1 + x ^ 2))) in H6.
  2 : { unfold f, g. extensionality x. lra. }

  rewrite H6. 
  unfold f.

  assert (H7 : 1 / √2 <= 1 / √(1 + ξ ^ 2) <= 1).
  {
    assert (H7 : √1 <= √(1 + ξ^2)) by (apply sqrt_le_1_alt; nra).
    rewrite sqrt_1 in H7.
    assert (H8 : √(1 + ξ^2) <= √2) by (apply sqrt_le_1_alt; solve_R).
    split.
    - apply Rmult_le_reg_l with (r := √2 * √(1 + ξ^2)); field_simplify; nra.
    - apply Rmult_le_reg_l with (r := √(1 + ξ^2)); field_simplify; nra.
  }

  pose proof sqrt_lt_R0 (1 + ξ ^ 2) ltac:(solve_R) as H8.
  split; apply Rmult_le_reg_r with (r := 7); field_simplify; try nra.
  apply sqrt2_neq_0. 
Qed.

Lemma lemma_14_7_ii :
  3 / 8 <= ∫ 0 (1/2) (fun x => √((1 - x) / (1 + x))) <= √3 / 4.
Proof.
  set (f := λ x, 1 / √(1 - x ^ 2)).
  set (g := λ x, 1 - x).

  assert (H1 : 0 < 1/2) by lra.
  assert (H2 : continuous_on f [0, 1/2]) by (unfold f; auto_cont).
  assert (H3 : integrable_on 0 (1/2) g) by (apply theorem_13_3; unfold g; auto_cont).
  assert (H4 : nonnegative_on g [0, 1/2]) by (intros x; unfold g; solve_R).

  pose proof lemma_13_23_d f g 0 (1/2) H1 H2 H3 H4 as [ξ [H5 H6]].

  replace (∫ 0 (1/2) g) with (3/8) in H6 by (symmetry; unfold g; auto_int).

  assert (H7 : ∫ 0 (1/2) (λ x : ℝ, √(g x / (1 + x))) = ∫ 0 (1/2) (f ⋅ g)).
  {
    apply integral_ext; [ lra | ].
    intros x H7.
    unfold f, g.
    assert (H8 : 0 <= 1 - x) by solve_R.
    assert (H9 : 0 < 1 + x) by solve_R.
    assert (H10 : 0 <= 1 - x^2) by solve_R.
    apply pow_eq_1 with (n := 2%nat); try lia.
    apply sqrt_lt_R0. apply Rdiv_pos_pos; solve_R.
    apply Rmult_pos_pos; solve_R. apply Rdiv_pos_pos; solve_R.
    apply sqrt_lt_R0; solve_R.
    rewrite pow2_sqrt; admit.
  }

  rewrite H7, H6.
  unfold f.

  assert (H8 : 1 <= √(1 - ξ^2) <= √3 / 2).
  {
    split.
    - rewrite <- sqrt_1 at 1.
      apply sqrt_le_1_alt.
      solve_R. admit.
    - admit.
  }

  pose proof sqrt_lt_R0 (1 - ξ^2) ltac:(solve_R) as H9.
  pose proof Rlt_sqrt3_0 as H10.

  split.
  - apply Rmult_le_reg_r with (r := 8 * √(1 - ξ^2));
      field_simplify;
      admit.
  - apply Rmult_le_reg_r with (r := 8 * √(1 - ξ^2) * √3);
      field_simplify;
      nra.
Admitted.