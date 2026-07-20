From Calculus.Chapter5 Require Import Prelude.
From Calculus.Chapter5 Require Import Problem34.

Section Problem35.

Variable α : R.
Hypothesis H1 : ⟦ lim 0 ⟧ (fun x => sin x / x) = α.

Lemma lemma_5_35_i : ⟦ lim ∞ ⟧ (fun x => sin x / x) = 0.
Proof.
  intros ε H2.
  exists (1 / ε).
  intros x H3.
  pose proof sin_bounds x as H4.
  simp_zero.
  apply Rmult_gt_compat_r with (r := ε) in H3; auto.
  field_simplify in H3; try lra.
  destruct (Rcase_abs (sin x / x)) as [H5 | H5];
  [ rewrite Rabs_left | rewrite Rabs_right ]; auto;
  apply Rmult_lt_reg_r with (r := x); field_simplify; solve_R.
Qed.

Lemma lemma_5_35_ii : ⟦ lim ∞ ⟧ (fun x => x * sin (1 / x)) = α.
Proof.
  assert (H2 : ⟦ lim 0⁺ ⟧ (λ x, sin x / x) = α) by (apply limit_iff; auto).
  pose proof lemma_5_34 (λ x, x * sin (1 / x)) α as H3.
  apply H3.
  replace (λ x : ℝ, 1 / x * sin (1 / (1 / x))) with (λ x, sin x / x); auto.
  extensionality x.
  repeat rewrite Rdiv_1_l.
  rewrite Rinv_inv. lra.
Qed.

End Problem35.