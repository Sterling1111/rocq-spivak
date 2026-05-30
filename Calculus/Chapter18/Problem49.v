From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_49 : irrational (log_ 10 2).
Proof.
  intros H1.
  pose proof H1 as [a [b H2]].
  pose proof log_b_pos 10 2 ltac:(lra) ltac:(lra) as H3.

  pose proof rational_representation_positive (log_ 10 2) H1 H3 as [a' [b' [H4 [H5 H6]]]].
  clear H1 H2 a b H3. 
  rename a' into a, b' into b, H4 into H1, H5 into H2, H6 into H3.

  Set Printing Coercions.




  symmetry in H1.
  apply log_b_spec in H1; try solve_R. 
  assert (H4 : 2 ^^ b = (10 ^^ (a / b)) ^^ b).
  { rewrite H1. reflexivity. }
  rewrite Rpower_mult in H4; try lra.
  assert (b = 0 \/ b <> 0)%Z as [H5 | H5] by lia.
  - subst. rewrite Rdiv_0_r, Rpower_0 in H1; lra.
  - replace (a / b * b) with (IZR a) in H2 by (field; apply not_0_IZR; auto).
    destruct (Z.eq_dec a 0) as [H6 | H6].
    + subst a. rewrite Rdiv_0_l, Rpower_0 in H1; lra.
    + Set Printing Coercions.
      replace (IZR a / IZR b * IZR b)%R with (IZR a) in H4 by solve_R.
      do 2 (rewrite Rpower_IZR_Znonneg in H4); try lra; apply lt_IZR in H2, H3; try lia.
      pose proof (z_pow_factor_primes 2 (Z.to_nat b) ltac:(lia)) as [l1 [H9 [H10 H11]]].
      pose proof (z_pow_factor_primes 10 (Z.to_nat a) ltac:(lia)) as [l2 [H12 [H13 H14]]].
      apply lt_IZR in H2, H3.
      do 2 rewrite Rpower_IZR_Znonneg in H4; try lra; try lia.
      assert (H15 : fold_right Z.mul 1%Z l1 = fold_right Z.mul 1%Z l2).
      {
        rewrite <- H10.
        rewrite <- H13.
        rewrite Z2Nat.id, Z2Nat.id; try lia.
        rewrite <- (Z2Nat.id b) by lia.
  rewrite <- (Z2Nat.id a) by lia.
  try rewrite <- !Zpower_nat_Z.
  pose proof prime_factorization_unique.
      }
      pose proof (prime_factorization_unique l1 l2 (fold_right Z.mul 1%Z l1) 5 H9 H12 eq_refl H15) as H16.
      destruct (H11 5) as [H17 H18].
      destruct (H14 5) as [H19 H20].
      rewrite H18 in H16.
      rewrite H20 in H16.
      admit.
Qed.