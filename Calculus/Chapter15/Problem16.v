From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_16 : ∀ x,
  sin (arctan x) = x / √(1 + x^2) /\ cos (arctan x) = 1 / √(1 + x^2).
Proof.
  intros x.
  set (y := arctan x).

  assert (H1 : x = tan y).
  { pose proof arctan_spec as [_ [_ [_ H1]]]. symmetry. apply H1. apply Full_intro. }

  unfold tan in H1. rewrite cos_eq_sqrt_1_minus_sin_sqr in H1.
  2 : { apply cos_arctan_nonneg. }
  assert (H2 : 0 < 1 - sin y ^ 2).
  { pose proof pythagorean_identity y as H2. pose proof cos_arctan_pos x as H3. fold y in H3. nra. }
  assert (H3 : √(1 - sin y ^ 2) > 0).
  { apply sqrt_lt_R0; auto. }

  assert (H4 : (√(1 - sin y ^ 2)) ^ 2 = 1 - sin y ^ 2).
  { apply pow2_sqrt. lra. }

  assert (H5 : 1 + x^2 = 1 / (√(1 - sin y ^ 2))^2).
  { 
    rewrite H1. 
    replace ((sin y / √(1 - sin y ^ 2))^2) with ((sin y)^2 / (√(1 - sin y ^ 2))^2).
    - rewrite H4. solve_R.
    - unfold Rdiv. rewrite Rpow_mult_distr. rewrite pow_inv. reflexivity. 
  }

  assert (H6 : √(1 + x^2) = 1 / √(1 - sin y ^ 2)).
  {
    rewrite H5.
    replace (1 / (√(1 - sin y ^ 2))^2) with ((1 / √(1 - sin y ^ 2)) ^ 2).
    - apply sqrt_pow2. apply Rlt_le. apply Rdiv_pos_pos; lra.
    - unfold Rdiv. rewrite Rpow_mult_distr. rewrite pow_inv. replace (1^2) with 1 by ring. reflexivity.
  }

  split.
  - rewrite H6, H1. field. lra.
  - rewrite cos_eq_sqrt_1_minus_sin_sqr; [| apply cos_arctan_nonneg].
    rewrite H6. field; lra.
Qed.