From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_18 : ∀ f a,
  (∀ x, ~ rational x -> f x = 0) ->
  (∀ x (p : ℤ) (q : ℤ), (q > 0)%Z -> x = p / q ->
    (∀ (p' : ℤ) (q' : ℤ), (q' > 0)%Z -> x = p' / q' -> (q <= q')%Z) ->
    f x = 1 / q) ->
  ~ differentiable_at f a.
Proof.
  intros f a H1 H2.
  assert (H3 : ∀ q : nat, (0 < q)%nat -> ∀ p : Z,
    1 / q <= f (p / q)).
  {
    induction q as [q IH] using lt_wf_ind. intros H3 p.
    destruct (classic (∀ (p' : ℤ) (q' : ℤ), (q' > 0)%Z -> p / q = p' / q' -> (Z.of_nat q <= q')%Z)) as [H4 | H4].
    - rewrite (H2 (p / q) p (Z.of_nat q)); auto; try lia.
      all: rewrite <- INR_IZR_INZ; auto; lra.
    - apply not_all_ex_not in H4 as [p' H4].
      apply not_all_ex_not in H4 as [q' H4].
      apply imply_to_and in H4 as [H4 H5].
      apply imply_to_and in H5 as [H5 H6].
      pose proof (IH (Z.to_nat q') ltac:(lia) ltac:(lia) p') as H7.
      rewrite INR_IZR_INZ, Z2Nat.id in H7; [| lia].
      rewrite H5. eapply Rle_trans; [| exact H7].
      assert (H8 : 0 < q' < q).
      { rewrite INR_IZR_INZ. split; apply IZR_lt; lia. }
      apply Rmult_le_reg_r with (r := q * q'); [nra |].
      field_simplify; lra.
  }
  intros H4.
  pose proof (differentiable_at_imp_continuous_at f a H4) as H5.
  assert (H6 : f a = 0).
  {
    destruct (Req_dec (f a) 0) as [H6 | H6]; auto.
    destruct (H5 (|f a|) ltac:(solve_R)) as [δ [H7 H8]].
    destruct (exists_irrational_between a (a + δ) ltac:(lra)) as [x [H9 H10]].
    specialize (H8 x ltac:(solve_R)). rewrite (H1 x H10) in H8. solve_R.
  }
  destruct H4 as [L H4].
  assert (H7 : L = 0).
  {
    destruct (Req_dec L 0) as [H7 | H7]; auto.
    destruct (H4 (|L|) ltac:(solve_R)) as [δ [H8 H9]].
    destruct (exists_irrational_between a (a + δ) ltac:(lra)) as [x [H10 H11]].
    specialize (H9 (x - a) ltac:(solve_R)).
    replace (a + (x - a)) with x in H9 by lra.
    rewrite H6, (H1 x H11) in H9. solve_R.
  }
  subst L.
  destruct (H4 1 ltac:(lra)) as [δ [H7 H8]].
  set (q := up (1 / δ)).
  assert (H9 : 0 < q /\ 1 / δ < q).
  { pose proof (archimed (1 / δ)). pose proof (Rdiv_pos_pos 1 δ ltac:(lra) H7). unfold q. lra. }
  set (p := up (a * q)).
  set (x := p / q).
  assert (H10 : 0 < x - a <= 1 / q).
  {
    pose proof (archimed (a * q)) as H10. unfold x, p.
    split.
    - apply Rmult_lt_reg_r with (r := (q : ℝ)); [lra |]. field_simplify; nra.
    - apply Rmult_le_reg_r with (r := (q : ℝ)); [lra |]. field_simplify; nra.
  }
  assert (H11 : 1 / q < δ).
  {
    apply Rmult_lt_reg_r with (r := (q : ℝ)); [lra |].
    field_simplify; [| lra].
    destruct H9 as [H9 H11].
    apply Rmult_lt_compat_r with (r := δ) in H11; [| lra].
    field_simplify in H11; lra.
  }
  assert (H12 : 1 / q <= f x).
  {
    pose proof (H3 (Z.to_nat q) ltac:(assert (0 < q)%Z by (apply lt_IZR; lra); lia) p) as H12.
    rewrite INR_IZR_INZ, Z2Nat.id in H12; [exact H12 | apply le_IZR; lra].
  }
  specialize (H8 (x - a) ltac:(solve_R)).
  replace (a + (x - a)) with x in H8 by lra. rewrite H6 in H8.
  assert (H13 : 1 <= (f x - 0) / (x - a)).
  { apply Rmult_le_reg_r with (r := x - a); [lra |]. field_simplify; lra. }
  solve_R.
Qed.
