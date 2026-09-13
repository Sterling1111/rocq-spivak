From Calculus.Chapter13 Require Import Prelude.
From Lib Require Import Sorted_Rlt.

Definition oscillation_lt (f : R -> R) (a b ε : R) : Prop :=
  ∃ m M,
    is_glb (λ y, ∃ x, x ∈ [a, b] /\ y = f x) m /\
    is_lub (λ y, ∃ x, x ∈ [a, b] /\ y = f x) M /\ M - m < ε.

Lemma partition_small_oscillation_13_30 : ∀ a b (bf : bounded_function_R a b)
  (P : partition a b) ε,
  U(bf, P) - L(bf, P) < ε * (b-a) ->
  ∃ i, (i < List.length (points a b P) - 1)%nat /\
    oscillation_lt (bounded_f a b bf) ((points a b P).[i]) ((points a b P).[i+1]) ε.
Proof.
  intros a b [f H1 H2] P ε H3. cbn in *.
  unfold upper_sum, lower_sum in H3; simpl in H3.
  destruct (partition_sublist_elem_has_sup f a b P H2) as [M [H4 H5]].
  destruct (partition_sublist_elem_has_inf f a b P H2) as [m [H6 H7]]. simpl in H3.
  pose proof partition_length a b P as H8.
  destruct (classic (∃ i, (i < List.length (points a b P)-1)%nat /\ M.[i]-m.[i] < ε))
    as [[i [H9 H10]] | H9].
  - exists i. split; auto. exists (m.[i]), (M.[i]). repeat split; auto;
      [apply (H7 i ltac:(lia)) | apply (H7 i ltac:(lia)) |
       apply (H5 i ltac:(lia)) | apply (H5 i ltac:(lia))].
  - assert (H10 : ∀ i, (i < List.length (points a b P)-1)%nat -> ε <= M.[i]-m.[i]).
    { intros i H10. destruct (Rle_lt_dec ε (M.[i]-m.[i])); auto.
      exfalso. apply H9. exists i. auto. }
    rewrite H4, H6, sum_f_minus in H3; try lia.
    assert (H11 : ε * (b-a) <=
      ∑ 0 (List.length (points a b P)-1-1) (λ i,
        M.[i]*((points a b P).[i+1]-(points a b P).[i]) -
        m.[i]*((points a b P).[i+1]-(points a b P).[i]))).
    {
      rewrite <- (partition_telescope a b P), r_mult_sum_f_i_n_f_l; try lia.
      replace (List.length (points a b P)-1-1)%nat with (List.length (points a b P)-2)%nat by lia.
      apply sum_f_congruence_le; try lia. intros i H11.
      pose proof Sorted_Rlt_nth (points a b P) i (i+1) 0 (partition_P2 a b P) ltac:(lia) as H12.
      specialize (H10 i ltac:(lia)). nra.
    }
    lra.
Qed.

Lemma integrable_small_oscillation_13_30 : ∀ f a b ε,
  a < b -> integrable_on a b f -> 0 < ε ->
  ∃ u v, a < u < v /\ v < b /\ oscillation_lt f u v ε.
Proof.
  intros f a b ε H1 H2 H3.
  pose proof integrable_imp_bounded f a b ltac:(lra) H2 as H4.
  set (bf := mkbounded_function_R a b f ltac:(lra) H4).
  pose proof (proj1 (theorem_13_2_a a b bf H1) H2 (ε*(b-a))
    ltac:(apply Rmult_lt_0_compat; lra)) as [P H5].
  pose proof partition_small_oscillation_13_30 a b bf P ε H5 as [i [H6 [m [M [H7 [H8 H9]]]]]].
  set (u := (2*(points a b P).[i] + (points a b P).[i+1])/3).
  set (v := ((points a b P).[i] + 2*(points a b P).[i+1])/3).
  pose proof Sorted_Rlt_nth (points a b P) i (i+1) 0 (partition_P2 a b P) ltac:(lia) as H10.
  pose proof partition_P5 a b P ((points a b P).[i]) ltac:(apply nth_In; lia) as H11.
  pose proof partition_P5 a b P ((points a b P).[i+1]) ltac:(apply nth_In; lia) as H12.
  assert (H13 : bounded_on f [u, v]).
  { apply bounded_on_sub_interval with (a := a) (b := b); auto. unfold u, v. lra. }
  destruct (interval_has_inf u v f ltac:(unfold u, v; lra) H13) as [m' H14].
  destruct (interval_has_sup u v f ltac:(unfold u, v; lra) H13) as [M' H15].
  assert (H16 : (λ y, exists x, x ∈ [u, v] /\ y = f x) ⊆
    (λ y, exists x, x ∈ [(points a b P).[i], (points a b P).[i+1]] /\ y = f x)).
  { intros y [x [H16 H17]]. exists x. split; auto. unfold u, v in H16. solve_R. }
  pose proof glb_subset _ _ _ _ H14 H7 H16 as H17.
  pose proof lub_subset _ _ _ _ H15 H8 H16 as H18.
  exists u, v. repeat split; try (unfold u, v; lra).
  exists m', M'. repeat split; auto; [apply H14 | apply H14 | apply H15 | apply H15 | lra].
Qed.

Lemma lemma_13_30_a : ∀ a b (bf : bounded_function_R a b) (P : partition a b),
  U(bf, P) - L(bf, P) < b - a ->
  ∃ i, (i < List.length (points a b P) - 1)%nat /\
    oscillation_lt (bounded_f a b bf) ((points a b P).[i]) ((points a b P).[i+1]) 1.
Proof.
  intros a b bf P H1. apply partition_small_oscillation_13_30. lra.
Qed.

Lemma lemma_13_30_b : ∀ f a b,
  a < b -> integrable_on a b f ->
  ∃ a1 b1, a < a1 < b1 /\ b1 < b /\ oscillation_lt f a1 b1 1.
Proof.
  intros f a b H1 H2. apply integrable_small_oscillation_13_30; auto; lra.
Qed.

Lemma lemma_13_30_c : ∀ f a b a1 b1,
  a < a1 < b1 -> b1 < b -> integrable_on a b f ->
  oscillation_lt f a1 b1 1 ->
  ∃ a2 b2, a1 < a2 < b2 /\ b2 < b1 /\ oscillation_lt f a2 b2 (1/2).
Proof.
  intros f a b a1 b1 H1 H2 H3 H4.
  apply integrable_small_oscillation_13_30; try lra.
  apply integrable_on_sub_interval with (a := a) (b := b); auto; lra.
Qed.

Lemma lemma_13_30_d : ∀ f a b,
  a < b -> integrable_on a b f ->
  ∃ (α β : nat -> R) x,
    (∀ (n : ℕ), (1 <= n)%nat ->
      a < α n < β n /\ β n < b /\
      α n < α (S n) /\ β (S n) < β n /\
      oscillation_lt f (α n) (β n) (1 / n) /\ x ∈ [α n, β n]) /\
    x ∈ (a, b) /\ continuous_at f x.
Abort.

Lemma lemma_13_30_e : ∀ f a b,
  a < b -> integrable_on a b f ->
  Infinite_set (λ x, x ∈ [a, b] /\ continuous_at f x).
Abort.
