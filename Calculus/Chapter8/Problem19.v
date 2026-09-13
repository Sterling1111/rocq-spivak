From Calculus.Chapter8 Require Import Prelude.
From Calculus.Chapter8 Require Import Problem18.

Definition lim_inf (A : Ensemble ℝ) (l : ℝ) :=
  is_lub (λ x, almost_lower_bound A x) l.

Lemma lemma_8_19_a : ∀ A li ls,
  Infinite_set A -> has_upper_bound A -> has_lower_bound A ->
  lim_inf A li -> lim_sup A ls -> li <= ls.
Proof.
  intros A li ls H1 H2 H3 H4 H5.
  apply (sup_le_inf _ _ li ls H4 H5).
  intros x y H6 H7. apply Rnot_lt_le. intros H8.
  apply H1, Finite_set_equiv_Finite.
  apply Finite_downward_closed with
    (A := (λ z, z ∈ A /\ z <= x) ⋃ (λ z, z ∈ A /\ z >= y)).
  - apply Union_preserves_Finite; apply Finite_set_equiv_Finite; assumption.
  - intros z H9. destruct (Rle_dec z x) as [H10 | H10].
    + left. split; auto.
    + right. split; [exact H9 | lra].
Qed.

Lemma lemma_8_19_b : ∀ A ls supa,
  Infinite_set A -> has_upper_bound A -> has_lower_bound A ->
  lim_sup A ls -> is_lub A supa -> ls <= supa.
Proof.
  intros A ls supa H1 H2 H3 [H4 H5] [H6 H7].
  apply Rge_le, H4.
  unfold almost_upper_bound. apply Finite_set_equiv_Finite.
  apply Finite_downward_closed with (A := ⦃supa⦄).
  - apply Singleton_is_finite.
  - intros x [H8 H9]. apply In_singleton_def.
    specialize (H6 x H8). lra.
Qed.

Lemma finite_set_has_greatest : ∀ A : Ensemble ℝ,
  Finite_set A -> A ≠ ∅ ->
  ∃ m, m ∈ A /\ is_upper_bound A m.
Proof.
  intros A H1. apply Finite_set_equiv_Finite in H1.
  induction H1 as [| A H1 IH x H2].
  - intros H3. contradiction.
  - intros H3. destruct (classic (A = ∅)) as [H4 | H4].
    + subst A. exists x. split.
      * right. constructor.
      * intros y H5. inversion H5 as [z H6 | z H6].
        -- inversion H6.
        -- inversion H6. lra.
    + destruct (IH H4) as [m [H5 H6]].
      destruct (Rle_dec x m) as [H7 | H7].
      * exists m. split; [left; exact H5 |].
        intros y H8. inversion H8 as [z H9 | z H9].
        -- apply H6, H9.
        -- inversion H9. lra.
      * exists x. split; [right; constructor |].
        intros y H8. inversion H8 as [z H9 | z H9].
        -- specialize (H6 y H9). lra.
        -- inversion H9. lra.
Qed.

Lemma lemma_8_19_c : ∀ A ls supa,
  Infinite_set A -> has_upper_bound A -> has_lower_bound A ->
  lim_sup A ls -> is_lub A supa -> ls < supa ->
  supa ∈ A.
Proof.
  intros A ls supa H1 H2 H3 [H4 H5] [H6 H7] H8.
  assert (H9 : ∃ t, almost_upper_bound A t /\ t < supa).
  { apply NNPP. intros H9.
    assert (H10 : is_lower_bound (λ t, almost_upper_bound A t) supa).
    { intros t H10. apply Rle_ge, Rnot_lt_le. intros H11.
      apply H9. exists t. split; auto. }
    specialize (H5 supa H10). lra. }
  destruct H9 as [t [H9 H10]].
  set (B := λ x, x ∈ A /\ x >= t).
  assert (H11 : B ≠ ∅).
  { apply not_Empty_In.
    destruct (exists_point_within_delta A supa (supa - t)
      ltac:(split; assumption) ltac:(lra)) as [x [H11 H12]].
    exists x. split; [exact H11 | lra]. }
  destruct (finite_set_has_greatest B H9 H11) as [m [[H12 H13] H14]].
  assert (H15 : is_upper_bound A m).
  { intros x H15. destruct (Rle_dec x t) as [H16 | H16]; [lra |].
    apply H14. split; [exact H15 | lra]. }
  specialize (H7 m H15). specialize (H6 m H12).
  replace supa with m by lra. exact H12.
Qed.
