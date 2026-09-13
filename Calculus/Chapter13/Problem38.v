From Calculus.Chapter13 Require Import Prelude.
From Lib Require Import Sorted_Rlt.
From Calculus.Chapter13 Require Import Problem36.

Section section_13_38.

Variable a b : ℝ.
Variables f g : ℝ → ℝ.
Variable P : partition a b.

Let l : list R := P.(points a b).

Hypothesis H1: a <= b.
Hypothesis H2 : integrable_on a b f.
Hypothesis H3 : integrable_on a b g.
Hypothesis H4 : ∀ x, x ∈ [a, b] -> f x >= 0.
Hypothesis H5 : ∀ x, x ∈ [a, b] -> g x >= 0.

Let H6 : bounded_on f [a, b] := integrable_imp_bounded f a b H1 H2.
Let H7 : bounded_on g [a, b] := integrable_imp_bounded g a b H1 H3.
Let H8 : bounded_on (f ⋅ g) [a, b] := bounded_on_mult f g a b H6 H7.

Let M'_list := proj1_sig (partition_sublist_elem_has_sup f a b P H6).
Let m'_list := proj1_sig (partition_sublist_elem_has_inf f a b P H6).
Let M''_list := proj1_sig (partition_sublist_elem_has_sup g a b P H7).
Let m''_list := proj1_sig (partition_sublist_elem_has_inf g a b P H7).
Let M_list := proj1_sig (partition_sublist_elem_has_sup (f ⋅ g) a b P H8).
Let m_list := proj1_sig (partition_sublist_elem_has_inf (f ⋅ g) a b P H8).

Let M' := λ i, M'_list.[i].
Let m' := λ i, m'_list.[i].
Let M'' := λ i, M''_list.[i].
Let m'' := λ i, m''_list.[i].
Let M := λ i, M_list.[i].
Let m := λ i, m_list.[i].

Lemma partition_lists_lengths :
  length M'_list = (length l - 1)%nat /\
  length m'_list = (length l - 1)%nat /\
  length M''_list = (length l - 1)%nat /\
  length m''_list = (length l - 1)%nat /\
  length M_list = (length l - 1)%nat /\
  length m_list = (length l - 1)%nat.
Proof.
  repeat split.
  - exact (proj1 (proj2_sig (partition_sublist_elem_has_sup f a b P H6))).
  - exact (proj1 (proj2_sig (partition_sublist_elem_has_inf f a b P H6))).
  - exact (proj1 (proj2_sig (partition_sublist_elem_has_sup g a b P H7))).
  - exact (proj1 (proj2_sig (partition_sublist_elem_has_inf g a b P H7))).
  - exact (proj1 (proj2_sig (partition_sublist_elem_has_sup (f ⋅ g) a b P H8))).
  - exact (proj1 (proj2_sig (partition_sublist_elem_has_inf (f ⋅ g) a b P H8))).
Qed.

Lemma lemma_13_38_a : ∀ (i : ℕ),
  M i <= M' i * M'' i /\ m i >= m' i * m'' i.
Proof.
  intros i.
  assert ((i >= (length l - 1))%nat \/ (i < (length l - 1))%nat) as [H9 | H9] by lia.
  - unfold M, M', M'', m, m', m''. repeat rewrite nth_overflow; pose proof partition_lists_lengths; try lia; lra.
  - assert (∀ x, x ∈ [l.[i], l.[i+1]] -> (0 <= m' i <= f x <= M' i) /\ (0 <= m'' i <= g x <= M'' i)) as H10.
    {
      intros x H10.
      pose proof partition_sublist_elem_is_inf f a b P H6 i H9 as [H11 H12].
      pose proof partition_sublist_elem_is_sup f a b P H6 i H9 as [H13 H14].
      pose proof partition_sublist_elem_is_inf g a b P H7 i H9 as [H15 H16].
      pose proof partition_sublist_elem_is_sup g a b P H7 i H9 as [H17 H18].
      fold l m' M' m'' M'' in H11, H12, H13, H14, H15, H16, H17, H18.
      assert (H19 : ∀ z, z ∈ [l.[i], l.[i+1]] -> z ∈ [a, b]).
      {
        intros z H19.
        pose proof partition_P5 a b P (l.[i]) ltac:(apply nth_In; unfold l in *; lia) as H20.
        pose proof partition_P5 a b P (l.[i+1]) ltac:(apply nth_In; unfold l in *; lia) as H21.
        solve_R.
      }
      repeat split.
      - apply Rge_le, H12. intros y [z [H20 H21]]. subst y. apply H4, H19, H20.
      - apply Rge_le, H11. exists x. auto.
      - apply H13. exists x. auto.
      - apply Rge_le, H16. intros y [z [H20 H21]]. subst y. apply H5, H19, H20.
      - apply Rge_le, H15. exists x. auto.
      - apply H17. exists x. auto.
    }
    pose proof partition_sublist_elem_is_sup (f ⋅ g) a b P H8 i H9 as [H11 H12].
    pose proof partition_sublist_elem_is_inf (f ⋅ g) a b P H8 i H9 as [H13 H14].
    split.
    + apply H12. intros y [x [H15 H16]].
      specialize (H10 x H15). change (y = f x * g x) in H16. nra.
    + apply H14. intros y [x [H15 H16]].
      specialize (H10 x H15). change (y = f x * g x) in H16. nra.
Qed.

Lemma lemma_13_38_b :
  let bf := mkbounded_function_R a b (f ⋅ g) H1 H8 in
  U(bf, P) - L(bf, P) <=
  ∑ 0 (List.length l - 2) (λ i,
    (M' i * M'' i - m' i * m'' i) * (l.[i+1] - l.[i])).
Proof.
  intros bf.
  change ((∑ 0 (length M_list - 1) (λ i, M i * (l.[i+1] - l.[i]))) -
    (∑ 0 (length m_list - 1) (λ i, m i * (l.[i+1] - l.[i]))) <=
    ∑ 0 (length l - 2) (λ i, (M' i * M'' i - m' i * m'' i) * (l.[i+1] - l.[i]))).
  destruct partition_lists_lengths as [H9 [H10 [H11 [H12 [H13 H14]]]]].
  rewrite H13, H14, sum_f_minus; try lia.
  replace (length l - 1 - 1)%nat with (length l - 2)%nat by lia.
  apply sum_f_congruence_le; try lia. intros i H15.
  pose proof lemma_13_38_a i as H16.
  pose proof Sorted_Rlt_nth l i (i+1) 0 (partition_P2 a b P)
    ltac:(pose proof partition_length a b P; unfold l in *; lia) as H17.
  fold M m. nra.
Qed.

Lemma lemma_13_38_c : ∀ B,
  (∀ x, x ∈ [a, b] -> |f x| <= B /\ |g x| <= B) ->
  let bf := mkbounded_function_R a b (f ⋅ g) H1 H8 in
  U(bf, P) - L(bf, P) <= B *
    ((∑ 0 (List.length l - 2) (λ i, (M' i - m' i) * (l.[i+1] - l.[i]))) +
     (∑ 0 (List.length l - 2) (λ i, (M'' i - m'' i) * (l.[i+1] - l.[i])))).
Proof.
  intros B H9 bf.
  apply Rle_trans with (r2 := ∑ 0 (length l - 2)
    (λ i, (M' i * M'' i - m' i * m'' i) * (l.[i+1] - l.[i]))).
  - apply lemma_13_38_b.
  - rewrite sum_f_plus, r_mult_sum_f_i_n_f_l; try lia.
    apply sum_f_congruence_le; try lia. intros i H10.
    assert (H11 : (i < length l - 1)%nat)
      by (pose proof partition_length a b P; unfold l in *; lia).
    pose proof partition_sublist_elem_is_inf f a b P H6 i H11 as H12.
    pose proof partition_sublist_elem_is_sup f a b P H6 i H11 as H13.
    pose proof partition_sublist_elem_is_inf g a b P H7 i H11 as H14.
    pose proof partition_sublist_elem_is_sup g a b P H7 i H11 as H15.
    fold l m' M' m'' M'' in H12, H13, H14, H15.
    assert (H16 : ∀ z, z ∈ [l.[i], l.[i+1]] -> z ∈ [a, b]).
    {
      intros z H16.
      pose proof partition_P5 a b P (l.[i]) ltac:(apply nth_In; unfold l in *; lia) as H17.
      pose proof partition_P5 a b P (l.[i+1]) ltac:(apply nth_In; unfold l in *; lia) as H18.
      solve_R.
    }
    assert (H17 : M' i <= B).
    { apply (proj2 H13). intros y [x [H17 H18]]. subst y.
      specialize (H9 x (H16 x H17)). solve_R. }
    assert (H18 : M'' i <= B).
    { apply (proj2 H15). intros y [x [H18 H19]]. subst y.
      specialize (H9 x (H16 x H18)). solve_R. }
    pose proof inf_le_sup _ _ _ H12 H13 as H19.
    pose proof inf_le_sup _ _ _ H14 H15 as H20.
    change (m' i <= M' i) in H19.
    change (m'' i <= M'' i) in H20.
    pose proof Rmult_le_compat_r (M' i - m' i) (M'' i) B ltac:(lra) H18 as H21a.
    pose proof Rmult_le_compat_r (M'' i - m'' i) (m' i) B ltac:(lra) ltac:(lra) as H21b.
    assert (H21 : M' i * M'' i - m' i * m'' i <=
      B * ((M' i - m' i) + (M'' i - m'' i))) by nra.
    pose proof Sorted_Rlt_nth l i (i+1) 0 (partition_P2 a b P) ltac:(unfold l in *; lia) as H22.
    replace (B * ((M' i - m' i) * (l.[i+1] - l.[i]) +
      (M'' i - m'' i) * (l.[i+1] - l.[i]))) with
      ((B * ((M' i - m' i) + (M'' i - m'' i))) * (l.[i+1] - l.[i])) by ring.
    apply Rmult_le_compat_r; lra.
Qed.

End section_13_38.

Lemma lemma_13_38_d : ∀ f g a b,
  a < b ->
  integrable_on a b f ->
  integrable_on a b g ->
  (∀ x, x ∈ [a, b] -> f x >= 0) ->
  (∀ x, x ∈ [a, b] -> g x >= 0) ->
  integrable_on a b (f ⋅ g).
Proof.
  intros f g a b H1 H2 H3 H4 H5.
  assert (H6 : a <= b) by lra.
  set (H7 := integrable_imp_bounded f a b H6 H2).
  set (H8 := integrable_imp_bounded g a b H6 H3).
  destruct H7 as [_ [Mf H9]]. destruct H8 as [_ [Mg H10]].
  set (B := |Mf| + |Mg| + 1).
  assert (H11 : 0 < B) by (unfold B; pose proof Rabs_pos Mf; pose proof Rabs_pos Mg; lra).
  assert (H12 : ∀ x, x ∈ [a, b] -> |f x| <= B /\ |g x| <= B).
  {
    intros x H12. specialize (H4 x H12). specialize (H5 x H12).
    specialize (H9 (f x) ltac:(exists x; auto)).
    specialize (H10 (g x) ltac:(exists x; auto)). unfold B. solve_R.
  }
  set (bf := mkbounded_function_R a b f H6 (integrable_imp_bounded f a b H6 H2)).
  set (bg := mkbounded_function_R a b g H6 (integrable_imp_bounded g a b H6 H3)).
  set (bfg := mkbounded_function_R a b (f ⋅ g) H6
    (bounded_on_mult f g a b (integrable_imp_bounded f a b H6 H2)
      (integrable_imp_bounded g a b H6 H3))).
  assert (H13 : ∀ (h : R -> R) (Hb : bounded_on h [a, b]) (P : partition a b),
    let bh := mkbounded_function_R a b h H6 Hb in
    U(bh, P) - L(bh, P) =
      ∑ 0 (List.length (points a b P) - 2) (λ i,
        ((proj1_sig (partition_sublist_elem_has_sup h a b P Hb)).[i] -
         (proj1_sig (partition_sublist_elem_has_inf h a b P Hb)).[i]) *
        ((points a b P).[i+1] - (points a b P).[i]))).
  {
    intros h Hb P bh. unfold upper_sum, lower_sum, bh; simpl.
    destruct (partition_sublist_elem_has_sup h a b P Hb) as [M [H13 H14]].
    destruct (partition_sublist_elem_has_inf h a b P Hb) as [m [H15 H16]]. simpl.
    rewrite H13, H15, sum_f_minus; try lia.
    replace (List.length (points a b P) - 1 - 1)%nat with
      (List.length (points a b P) - 2)%nat by lia.
    apply sum_f_congruence; try lia. intros i H17. ring.
  }
  change (integrable_on a b (bounded_f a b bfg)).
  apply (proj2 (theorem_13_2_a a b bfg H1)). intros ε H14.
  assert (H15 : ε / (2 * B) > 0) by (apply Rdiv_lt_0_compat; lra).
  pose proof (proj1 (theorem_13_2_a a b bf H1) H2 _ H15) as [P1 H16].
  pose proof (proj1 (theorem_13_2_a a b bg H1) H3 _ H15) as [P2 H17].
  pose proof exists_partition_includes_both a b P1 P2 as [P [H18 H19]].
  exists P.
  pose proof lemma_13_1_a a b bf P P1 H18 as H20.
  pose proof lemma_13_1_b a b bf P P1 H18 as H21.
  pose proof lemma_13_1_a a b bg P P2 H19 as H22.
  pose proof lemma_13_1_b a b bg P P2 H19 as H23.
  pose proof lemma_13_38_c a b f g P H6 H2 H3 H4 H5 B H12 as H24.
  cbn zeta beta in H24. rewrite <- !H13 in H24. fold bf bg bfg in H24.
  apply Rle_lt_trans with (r2 := B * ((U(bf, P) - L(bf, P)) + (U(bg, P) - L(bg, P)))); auto.
  replace ε with (B * (ε / (2 * B) + ε / (2 * B))) by (field; lra).
  apply Rmult_lt_compat_l; lra.
Qed.

Lemma lemma_13_38_e : ∀ f g a b,
  a < b ->
  integrable_on a b f ->
  integrable_on a b g ->
  integrable_on a b (f ⋅ g).
Proof.
  intros f g a b H1 H2 H3.
  set (fp := λ x, Rmax (f x) 0).
  set (fn := λ x, - Rmin (f x) 0).
  set (gp := λ x, Rmax (g x) 0).
  set (gn := λ x, - Rmin (g x) 0).
  pose proof (proj1 (lemma_13_36_d f a b H1) H2) as [H4 H5].
  pose proof (proj1 (lemma_13_36_d g a b H1) H3) as [H6 H7].
  assert (H8 : integrable_on a b fn).
  { unfold fn. replace (λ x, - Rmin (f x) 0) with
      (λ x, -1 * Rmin (f x) 0) by (extensionality x; ring).
    apply integrable_mult_scalar; auto. }
  assert (H9 : integrable_on a b gn).
  { unfold gn. replace (λ x, - Rmin (g x) 0) with
      (λ x, -1 * Rmin (g x) 0) by (extensionality x; ring).
    apply integrable_mult_scalar; auto. }
  assert (H10 : integrable_on a b (fp ⋅ gp)).
  { apply lemma_13_38_d; auto; intros x H10; unfold fp, gp; solve_R. }
  assert (H11 : integrable_on a b (fn ⋅ gn)).
  { apply lemma_13_38_d; auto; intros x H11; unfold fn, gn; solve_R. }
  assert (H12 : integrable_on a b (fp ⋅ gn)).
  { apply lemma_13_38_d; auto; intros x H12; unfold fp, gn; solve_R. }
  assert (H13 : integrable_on a b (fn ⋅ gp)).
  { apply lemma_13_38_d; auto; intros x H13; unfold fn, gp; solve_R. }
  replace (f ⋅ g) with (λ x, (fp x * gp x + fn x * gn x) - (fp x * gn x + fn x * gp x)).
  2 : { extensionality x. unfold fp, fn, gp, gn. solve_R. }
  apply integrable_minus; try lra; apply integrable_plus; auto.
Qed.
