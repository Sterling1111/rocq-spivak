From Calculus.Chapter13 Require Import Prelude.
From Lib Require Import Sorted_Rlt.

Lemma lemma_13_20_a : ∀ a b (bf : bounded_function_R a b) (P : partition a b),
  let f := bounded_f a b bf in
  let t := points a b P in
  non_decreasing_on f [a, b] ->
  L(bf, P) = (∑ 0 (List.length t - 2) (λ i, f (t.[i]) * (t.[i+1] - t.[i]))) /\
  U(bf, P) = (∑ 0 (List.length t - 2) (λ i, f (t.[i+1]) * (t.[i+1] - t.[i]))).
Proof.
  intros a b [f H1 H2] P. cbn zeta. intros H3.
  pose proof partition_length a b P as H4.
  assert (H5 : ∀ i, (i < List.length (points a b P) - 1)%nat ->
    is_glb (λ y, exists x,
      x ∈ [(points a b P).[i], (points a b P).[i+1]] /\ y = f x)
      (f ((points a b P).[i])) /\
    is_lub (λ y, exists x,
      x ∈ [(points a b P).[i], (points a b P).[i+1]] /\ y = f x)
      (f ((points a b P).[i+1]))).
  {
    intros i H5.
    pose proof partition_P5 a b P ((points a b P).[i]) ltac:(apply nth_In; lia) as H6.
    pose proof partition_P5 a b P ((points a b P).[i+1]) ltac:(apply nth_In; lia) as H7.
    pose proof Sorted_Rlt_nth (points a b P) i (i+1) 0
      (partition_P2 a b P) ltac:(lia) as H8.
    repeat split.
    - intros y [x [H9 H10]]. subst y. apply Rle_ge, H3; solve_R.
    - intros c H9. apply H9. exists ((points a b P).[i]). split; [solve_R | reflexivity].
    - intros y [x [H9 H10]]. subst y. apply H3; solve_R.
    - intros c H9. apply H9. exists ((points a b P).[i+1]). split; [solve_R | reflexivity].
  }
  split.
  - unfold lower_sum; simpl.
    destruct (partition_sublist_elem_has_inf f a b P H2) as [l [H6 H7]]. simpl.
    replace (List.length l - 1)%nat with (List.length (points a b P) - 2)%nat by lia.
    apply sum_f_congruence; try lia. intros i H8.
    rewrite (glb_unique _ _ _ (H7 i ltac:(lia)) (proj1 (H5 i ltac:(lia)))). reflexivity.
  - unfold upper_sum; simpl.
    destruct (partition_sublist_elem_has_sup f a b P H2) as [l [H6 H7]]. simpl.
    replace (List.length l - 1)%nat with (List.length (points a b P) - 2)%nat by lia.
    apply sum_f_congruence; try lia. intros i H8.
    rewrite (lub_unique _ _ _ (H7 i ltac:(lia)) (proj2 (H5 i ltac:(lia)))). reflexivity.
Qed.

Lemma lemma_13_20_b : ∀ a b (bf : bounded_function_R a b) (P : partition a b) δ,
  let f := bounded_f a b bf in
  let t := points a b P in
  non_decreasing_on f [a, b] ->
  (∀ i, (i < List.length t - 1)%nat -> t.[i+1] - t.[i] = δ) ->
  U(bf, P) - L(bf, P) = δ * (f b - f a).
Proof.
  intros a b bf P δ f t H1 H2.
  pose proof lemma_13_20_a a b bf P H1 as [H3 H4].
  rewrite H3, H4, sum_f_minus; try lia. fold f t.
  transitivity (δ * ∑ 0 (List.length t - 2) (λ i, f (t.[i+1]) - f (t.[i]))).
  - rewrite r_mult_sum_f_i_n_f_l; try lia.
    apply sum_f_congruence; try lia. intros i H5.
    rewrite H2 by (pose proof partition_length a b P; unfold t in *; lia). ring.
  - rewrite (sum_f_0_n_fSi_minus_fi _ (λ i, f (t.[i]))).
    replace (List.length t - 2 + 1)%nat with (List.length t - 1)%nat
      by (pose proof partition_length a b P; unfold t in *; lia).
    unfold t. rewrite partition_first, partition_last. reflexivity.
Qed.

Lemma lemma_13_20_c : ∀ f a b,
  a < b ->
  non_decreasing_on f [a, b] ->
  integrable_on a b f.
Proof.
  intros f a b H1 H2.
  assert (H3 : bounded_on f [a, b]).
  {
    split; [exists (f a) | exists (f b)]; intros y [x [H3 H4]]; subst y.
    - apply Rle_ge, H2; solve_R.
    - apply H2; solve_R.
  }
  set (bf := mkbounded_function_R a b f ltac:(lra) H3).
  change (integrable_on a b (bounded_f a b bf)).
  apply (proj2 (theorem_13_2_a a b bf H1)). intros ε H4.
  pose proof exists_nat_gt_inv_scale a b (ε / (f b - f a + 1)) H1
    ltac:(assert (f a <= f b) by (apply H2; solve_R); apply Rdiv_lt_0_compat; lra)
    as [n [H5 H6]].
  exists (uniform_partition a b n H1 H5).
  rewrite (lemma_13_20_b a b bf _ ((b-a) / n)); auto.
  - simpl. assert (H7 : 0 <= f b - f a) by (assert (f a <= f b) by (apply H2; solve_R); lra).
    assert (H8 : 0 < (b-a) / n) by (apply Rdiv_lt_0_compat; [lra | apply lt_0_INR; lia]).
    assert (H9 : (b-a) / n * (f b - f a + 1) < ε).
    { apply Rlt_le_trans with (r2 := ε / (f b - f a + 1) * (f b - f a + 1)).
      - apply Rmult_lt_compat_r; lra.
      - right. field. lra. }
    nra.
  - intros i H7. apply uniform_partition_width. exact H7.
Qed.

Lemma lemma_13_20_d : ∃ f : R -> R,
  non_decreasing_on f [0, 1] /\
  Infinite_set (λ x, x ∈ (0, 1) /\ ~ continuous_at f x).
Abort.
