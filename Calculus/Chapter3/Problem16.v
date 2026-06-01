From Calculus.Chapter3 Require Export Prelude.
From Calculus.Chapter1 Require Import Problem24.


Lemma lemma_3_16_a : forall (f : R -> R) l,
  (forall x y, f(x + y) = f x + f y) -> f (standard_sum l) = standard_sum (map f l).
Proof.
  intros f l.
  induction l as [|a l IHl].
  - intros H1. simpl. specialize (H1 0 0). rewrite Rplus_0_r in H1. nra.
  - intros H1. simpl. destruct l.
    -- simpl. reflexivity.
    -- simpl. rewrite H1. apply Rplus_eq_compat_l. simpl in IHl. apply IHl. apply H1.
Qed.

Lemma lemma_3_16_b : forall f : R -> R, 
  (forall x y, f (x + y) = f x + f y) -> 
  exists c : R, forall x, rational x -> f x = c * x.
Proof.
  intros f H1.
  exists (f 1).
  intros x H2.
  assert (H3 : forall n : nat, f n = f 1 * n).
  {
    induction n as [| k IH].
    - pose proof (H1 0 0) as H3. rewrite Rplus_0_l in H3. solve_R.
    - replace (S k) with (k + 1)%nat by lia. rewrite plus_INR, H1. 
      replace (INR 1) with 1 by auto. lra.
  }
  assert (H4 : forall x : R, f (- x) = - f x).
  {
    intros y.
    pose proof (H1 y (-y)) as H4.
    replace (y + -y) with 0 in H4 by lra.
    assert (H5 : f 0 = 0).
    { specialize (H1 0 0). rewrite Rplus_0_r in H1. lra. }
    lra.
  }
  assert (H5 : forall (m : nat) (y : R), f (m * y) = m * f y).
  {
    intros m y. induction m as [| k IH].
    - simpl. replace (0 * y) with 0 by lra.
      assert (H7 : f 0 = 0).
      { specialize (H1 0 0). rewrite Rplus_0_r in H1. lra. }
      rewrite H7. lra.
    - replace (S k) with (k + 1)%nat by lia.
      rewrite plus_INR.
      rewrite Rmult_plus_distr_r, H1, IH. 
      replace (INR 1) with 1 by auto.
      rewrite Rmult_1_l. lra.
  }
  assert (H6 : forall n : nat, (n <> 0)%nat -> f (/ n) = f 1 * / n).
  {
    intros n H6.
    specialize (H5 n (/ n)).
    apply not_0_INR in H6.
    replace (n * / n) with 1 in H5 by solve_R.
    solve_R.
  }
  assert (H7 : ∀ n : ℕ, (n <> 0)%nat -> f (/ (-n)) = f 1 * (/ (-n))).
  {
    intros n H7.
    replace (/ (-n)) with (- (/ n)) by (solve_R; apply not_0_INR; auto).
    rewrite H4, H6; solve_R.
    apply not_0_INR; auto.
  }
  assert (H8 : forall (z : Z) (y : R), f (z * y) = z * f y).
  { 
    intros z w.
    assert (z = 0 \/ z > 0 \/ z < 0)%Z as [H9 | [H9 | H9]] by lia.
    - subst. repeat rewrite Rmult_0_l. specialize (H1 0 0). rewrite Rplus_0_l in H1. lra.
    - replace (IZR z) with (INR (Z.to_nat z)).
      2 : { rewrite INR_IZR_INZ, Z2Nat.id; solve_R. }
      apply H5.
    - replace (IZR z) with (- IZR (- z)) by (rewrite opp_IZR; lra).
      replace (- IZR (- z) * w) with (- (IZR (- z) * w)) by lra.
      rewrite H4.
      replace (IZR (- z)) with (INR (Z.to_nat (- z))) by (rewrite INR_IZR_INZ, Z2Nat.id; solve_R).
      rewrite H5. lra.
  }
  destruct H2 as [z1 [z2 H9]].
  assert (z2 = 0 \/ z2 > 0 \/ z2 < 0)%Z as [H10 | [H10 | H10]] by lia.
  - subst. rewrite Rdiv_0_r. 
    specialize (H1 0 0). rewrite Rplus_0_l in H1. lra.
  - rewrite H9. unfold Rdiv. rewrite H8.
    replace (IZR z2) with (INR (Z.to_nat z2)).
    2 : { rewrite INR_IZR_INZ, Z2Nat.id; solve_R. }
    rewrite H6; [ lra | lia ].
  - rewrite H9. unfold Rdiv. rewrite H8.
    replace (IZR z2) with (- INR (Z.to_nat (- z2))).
    2 : { rewrite INR_IZR_INZ, Z2Nat.id; try lia. rewrite <- opp_IZR. apply IZR_eq. lia. }
    rewrite H7; [ lra | lia ].
Qed.