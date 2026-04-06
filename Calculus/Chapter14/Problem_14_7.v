From Calculus.Chapter14 Require Import Prelude.
From Calculus.Chapter13 Require Import Problem_13_23.
Require Import Interval.Tactic.

Lemma lemma_14_7_i :
  1 / (7 * √2) <= ∫ 0 1 (fun x => x^6 / √(1 + x^2)) <= 1 / 7.
Proof.
  set (f := λ x, 1 / √(1 + x ^ 2)).
  set (g := λ x, x^6).

  assert (H1 : 0 < 1) by lra.
  assert (H2 : continuous_on f [0, 1]).
  {
    unfold f. auto_cont. intros H2.
    apply Rmult_eq_compat_r with (r := √(1 + a * (a * 1))) in H2.
    rewrite Rmult_0_l, sqrt_sqrt in H2; nra.
  }
  assert (H3 : integrable_on 0 1 g) by (apply theorem_13_3; unfold g; auto_cont).
  assert (H4 : nonnegative_on g [0, 1]) by (intros x H4; unfold g; nra).

  pose proof lemma_13_23_d f g 0 1 H1 H2 H3 H4 as [ξ [H5 H6]].

  replace (∫ 0 1 g) with (1/7) in H6.
  2 : {
    symmetry.
    set (G := λ x : ℝ, x^7 / 7).
    assert (H7 : continuous_on g [0, 1]) by (unfold g; auto_cont).
    assert (H8 : ⟦ der ⟧ G [0, 1] = (λ x : ℝ, x^6)) by (unfold G; auto_diff).
    replace (1 / 7) with (G 1 - G 0) by (unfold G; lra).
    apply (FTC2 0 1 (λ x : ℝ, x^6) G H1 H7 H8).
  }

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
  assert (H2 : continuous_on f [0, 1/2]).
  {
    unfold f. auto_cont. intros H2.
    apply Rmult_eq_compat_r with (r := √(1 - a * (a * 1))) in H2.
    rewrite Rmult_0_l, sqrt_sqrt in H2; nra.
  }
  assert (H3 : integrable_on 0 (1/2) g) by (apply theorem_13_3; unfold g; auto_cont).
  assert (H4 : nonnegative_on g [0, 1/2]) by (intros x; unfold g; solve_R).

  pose proof lemma_13_23_d f g 0 (1/2) H1 H2 H3 H4 as [ξ [H5 H6]].

  replace (∫ 0 (1/2) g) with (3/8) in H6.
  2 : {
    symmetry.
    set (G := λ x : ℝ, x - x^2 / 2).
    assert (H7 : continuous_on g [0, 1/2]) by (unfold g; auto_cont).
    assert (H8 : ⟦ der ⟧ G [0, 1/2] = (λ x : ℝ, 1 - x)) by (unfold G; auto_diff).
    replace (3 / 8) with (G (1/2) - G 0) by (unfold G; lra).
    apply (FTC2 0 (1/2) (λ x : ℝ, 1 - x) G H1 H7 H8).
  }

  replace (f ⋅ g) with (λ x : ℝ, √((1 - x) / (1 + x))) in H6.
  2 : { 
    unfold f, g. extensionality x. admit.
  }
  unfold g, f.
  rewrite H6. 

  assert (H7 : 1 <= 1 / √(1 - ξ ^ 2) <= 2 / √3).
  {
    admit.
  }

  split.
  - destruct H7 as [H7 _].
    apply Rmult_le_compat_r with (r := 3/8) in H7; try nra. admit. 
  - destruct H7 as [_ H7].
    assert (H8 : (2 / √3) * (3 / 8) = √3 / 4).
    { 
      admit. 
    }
    admit.
Admitted.