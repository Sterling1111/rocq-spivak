From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_16_sin : forall x,
  sin (arctan x) = x / √(1 + x^2).
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
  rewrite H1.

  set (z := sin y) in *.
  set (w := √(1 - z^2)) in *.

  assert (H4 : w ^ 2 = 1 - z ^ 2).
  { unfold w. apply pow2_sqrt. lra. }

  assert (H5 : 1 + (z / w)^2 = 1 / w^2).
  { replace ((z / w)^2) with (z^2 / w^2) by (field; lra). solve_R. }
  rewrite H5.

  assert (H6 : √(1 / w^2) = 1 / w).
  {
    replace (1 / w^2) with ((1 / w) * (1 / w)) by (field; lra).
    apply sqrt_square.
    apply Rlt_le. apply Rdiv_pos_pos; lra.
  }
  
  rewrite H6. solve_R.
Qed.

Lemma lemma_15_16_cos : forall x,
  cos (arctan x) = 1 / √(1 + x^2).
Abort.
