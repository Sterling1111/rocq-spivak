From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_10 : ∀ α β,
  -1 <= α <= 1 -> -1 <= β <= 1 ->
  α^2 + β^2 <= 1 ->
  arcsin α + arcsin β = arcsin (α * √(1 - β^2) + β * √(1 - α^2)).
Proof.
  intros α β H1 H2 H3.
  pose proof arcsin_spec as [H4 [H5 [H6 H7]]].
  assert (H8 : arcsin α ∈ [- (π / 2), π / 2]) by (apply H5; exact H1).
  assert (H9 : arcsin β ∈ [- (π / 2), π / 2]) by (apply H5; exact H2).
  assert (H10 : sin (arcsin α) = α) by (apply H7; exact H1).
  assert (H11 : sin (arcsin β) = β) by (apply H7; exact H2).
  assert (H12 : ∀ t, t ∈ [- (π / 2), π / 2] -> 0 <= cos t).
  { intros t H12. destruct (Rle_dec 0 t) as [H13 | H13].
    - apply cos_sign_q1. split; solve_R.
    - rewrite <- cos_even_odd. apply cos_sign_q1. split; solve_R. }
  pose proof H12 _ H8 as H13.
  pose proof H12 _ H9 as H14.
  assert (H15 : cos (arcsin α) = √(1 - α^2)).
  { rewrite cos_eq_sqrt_1_minus_sin_sqr; [rewrite H10; reflexivity | exact H13]. }
  assert (H16 : cos (arcsin β) = √(1 - β^2)).
  { rewrite cos_eq_sqrt_1_minus_sin_sqr; [rewrite H11; reflexivity | exact H14]. }
  assert (H17 : 0 <= cos (arcsin α + arcsin β)).
  { rewrite cos_plus, H10, H11.
    pose proof pythagorean_identity (arcsin α) as H17.
    pose proof pythagorean_identity (arcsin β) as H18.
    rewrite H10 in H17. rewrite H11 in H18.
    assert (H19 : (cos (arcsin α) * cos (arcsin β))^2 - (α * β)^2 = 1 - α^2 - β^2).
    { replace ((cos (arcsin α) * cos (arcsin β))^2) with
        ((cos (arcsin α))^2 * (cos (arcsin β))^2) by ring.
      replace ((cos (arcsin α))^2) with (1 - α^2) by lra.
      replace ((cos (arcsin β))^2) with (1 - β^2) by lra. ring. }
    pose proof Rmult_le_pos _ _ H13 H14 as H20. nra. }
  assert (H18 : (arcsin α + arcsin β) ∈ [- (π / 2), π / 2]).
  { pose proof π_pos as H18.
    assert (H19 : -π <= arcsin α + arcsin β <= π) by solve_R.
    destruct (Rlt_dec (π / 2) (arcsin α + arcsin β)) as [H20 | H20].
    - pose proof cos_lt_0 (arcsin α + arcsin β) ltac:(lra). lra.
    - destruct (Rlt_dec (arcsin α + arcsin β) (- (π / 2))) as [H21 | H21].
      + pose proof cos_lt_0 (- (arcsin α + arcsin β)) ltac:(lra) as H22.
        rewrite cos_even_odd in H22. lra.
      + split; lra. }
  rewrite <- (H6 _ H18).
  f_equal. rewrite sin_plus, H10, H11, H15, H16. ring.
Qed.
