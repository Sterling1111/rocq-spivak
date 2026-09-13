From Calculus.Chapter13 Require Import Prelude.
From Lib Require Import Sorted_Rlt.

Lemma lemma_13_36_a : ∀ f a b (P : partition a b) i M m M' m',
  bounded_on f [a, b] ->
  let t := points a b P in
  (i < List.length t - 1)%nat ->
  is_lub (λ y, ∃ x, x ∈ [t.[i], t.[i+1]] /\ y = f x) M ->
  is_glb (λ y, ∃ x, x ∈ [t.[i], t.[i+1]] /\ y = f x) m ->
  is_lub (λ y, ∃ x, x ∈ [t.[i], t.[i+1]] /\ y = |f x|) M' ->
  is_glb (λ y, ∃ x, x ∈ [t.[i], t.[i+1]] /\ y = |f x|) m' ->
  M' - m' <= M - m.
Proof.
  intros f a b P i M m M' m' H1 t H2 H3 H4 H5 H6.
  assert (H7 : ∀ x, x ∈ [t.[i], t.[i+1]] -> m <= f x <= M).
  {
    intros x H7. split.
    - apply Rge_le, (proj1 H4). exists x. auto.
    - apply (proj1 H3). exists x. auto.
  }
  assert (H8 : M' <= m' + (M - m)).
  {
    apply (proj2 H5). intros y [x [H8 H9]]. subst y.
    assert (H10 : m' >= |f x| - (M - m)).
    {
      apply (proj2 H6). intros y [z [H10 H11]]. subst y.
      pose proof H7 x H8 as H12. pose proof H7 z H10 as H13.
      solve_R.
    }
    lra.
  }
  lra.
Qed.

Lemma lemma_13_36_b : ∀ f a b,
  a < b ->
  integrable_on a b f ->
  integrable_on a b (λ x, |f x|).
Proof.
  intros f a b H1 H2.
  pose proof integrable_imp_bounded f a b ltac:(lra) H2 as H3.
  assert (H4 : bounded_on (λ x, |f x|) [a, b]).
  {
    destruct H3 as [[m H3] [M H4]]. split.
    - exists 0. intros y [x [H5 H6]]. subst y. pose proof Rabs_pos (f x). lra.
    - exists (Rmax (-m) M). intros y [x [H5 H6]]. subst y.
      pose proof H3 (f x) ltac:(exists x; auto) as H7.
      pose proof H4 (f x) ltac:(exists x; auto) as H8. solve_R.
  }
  set (bf := mkbounded_function_R a b f ltac:(lra) H3).
  set (bg := mkbounded_function_R a b (λ x, |f x|) ltac:(lra) H4).
  change (integrable_on a b (bounded_f a b bg)).
  apply (proj2 (theorem_13_2_a a b bg H1)). intros ε H5.
  pose proof (proj1 (theorem_13_2_a a b bf H1) H2 ε H5) as [P H6].
  exists P. apply Rle_lt_trans with (r2 := U(bf, P) - L(bf, P)); auto.
  unfold upper_sum, lower_sum, bf, bg; simpl.
  destruct (partition_sublist_elem_has_sup (λ x, |f x|) a b P H4) as [M' [H7 H8]].
  destruct (partition_sublist_elem_has_inf (λ x, |f x|) a b P H4) as [m' [H9 H10]].
  destruct (partition_sublist_elem_has_sup f a b P H3) as [M [H11 H12]].
  destruct (partition_sublist_elem_has_inf f a b P H3) as [m [H13 H14]]. simpl.
  rewrite H7, H9, H11, H13, !sum_f_minus; try lia.
  apply sum_f_congruence_le; try lia. intros i H15.
  pose proof partition_length a b P as H16.
  pose proof lemma_13_36_a f a b P i (M.[i]) (m.[i]) (M'.[i]) (m'.[i]) H3
    ltac:(lia) (H12 i ltac:(lia)) (H14 i ltac:(lia))
    (H8 i ltac:(lia)) (H10 i ltac:(lia)) as H17.
  pose proof Sorted_Rlt_nth (points a b P) i (i+1) 0
    (partition_P2 a b P) ltac:(lia) as H18.
  nra.
Qed.

Lemma lemma_13_36_c : ∀ f g a b,
  a < b ->
  integrable_on a b f ->
  integrable_on a b g ->
  integrable_on a b (λ x, Rmax (f x) (g x)) /\
  integrable_on a b (λ x, Rmin (f x) (g x)).
Proof.
  intros f g a b H1 H2 H3.
  assert (H4 : integrable_on a b (λ x, |f x - g x|)).
  { apply lemma_13_36_b; auto. apply integrable_minus; auto; lra. }
  assert (H5 : integrable_on a b (f + g)%function) by (apply integrable_plus; auto).
  split.
  - replace (λ x, Rmax (f x) (g x)) with
      (λ x, (1/2) * (f x + g x + |f x - g x|))
      by (extensionality x; solve_R).
    apply integrable_mult_scalar; auto. apply integrable_plus; auto.
  - replace (λ x, Rmin (f x) (g x)) with
      (λ x, (1/2) * (f x + g x - |f x - g x|))
      by (extensionality x; solve_R).
    apply integrable_mult_scalar; auto. apply integrable_minus; auto; lra.
Qed.

Lemma lemma_13_36_d : ∀ f a b,
  a < b ->
  (integrable_on a b f <->
   integrable_on a b (λ x, Rmax (f x) 0) /\
   integrable_on a b (λ x, Rmin (f x) 0)).
Proof.
  intros f a b H1. split.
  - intros H2. apply lemma_13_36_c; auto.
    apply theorem_13_3; try lra. auto_cont.
  - intros [H2 H3].
    replace f with (λ x, Rmax (f x) 0 + Rmin (f x) 0)
      by (extensionality x; solve_R).
    apply integrable_plus; auto.
Qed.
