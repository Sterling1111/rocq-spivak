From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_19_a : ∀ f f' g h h' a,
  f a = g a = h a ->
  (∀ x, f x <= g x <= h x) ->
  ⟦ der a ⟧ f = f' -> ⟦ der a ⟧ h = h' ->
  f' a = h' a ->
  differentiable_at g a /\ ∃ g', ⟦ der a ⟧ g = g' /\ g' a = f' a = h' a.
Proof.
  intros f f' g h h' a [H1 H2] H3 H4 H5 H6.

  assert (⟦ der_ a ⟧ g = f' a) as H7.
  {
    apply limit_squeeze with 
    (f1 := (λ h0, if Rle_dec 0 h0 then (f (a + h0) - f a) / h0 else (h (a + h0) - h a) / h0)) 
    (f3 := (λ h0, if Rle_dec 0 h0 then (h (a + h0) - h a) / h0 else (f (a + h0) - f a) / h0)) 
    (a := -1) (b := 1);
    try solve [solve_R].
    - intros ε H7.
      destruct (H4 ε H7) as [δ1 [H8 H9]].
      destruct (H5 ε H7) as [δ2 [H10 H11]].
      exists (Rmin δ1 δ2).
      split; [solve_R|].
      intros x [H12 H13].
      destruct (Rle_dec 0 x) as [H14 | H15].
      + apply H9. solve_R.
      + rewrite H6. apply H11; solve_R.
    - intros ε H7.
      destruct (H4 ε H7) as [δ1 [H8 H9]].
      destruct (H5 ε H7) as [δ2 [H10 H11]].
      exists (Rmin δ1 δ2).
      split; [solve_R|].
      intros x [H12 H13].
      destruct (Rle_dec 0 x) as [H14 | H15].
      + rewrite H6. apply H11. solve_R.
      + apply H9; solve_R.
    - intros x H7.
      destruct (H3 (a + x)) as [H8 H9].
      apply In_Union_def in H7.
      destruct (Rle_dec 0 x) as [H10 | H10].
      + split; apply Rmult_le_reg_r with (r := x); field_simplify; solve_R.
      + apply Rnot_le_lt in H10. 
        assert (H11 : / x < 0) by (apply Rinv_lt_0_compat; exact H10).
        split; [ rewrite <- H2 | rewrite <- H1]; nra.
  }

  split.
  - exists (f' a); exact H7.
  - exists f'; auto.
Qed.

Lemma lemma_9_19_b : ~ (forall f f' g h h' a,
  (forall x, f x <= g x <= h x) ->
  ⟦ der a ⟧ f = f' -> ⟦ der a ⟧ h = h' ->
  f' a = h' a ->
  exists g', ⟦ der a ⟧ g = g' /\ g' a = f' a).
Proof.
  intros H1.
  specialize (H1 (λ _, -1) (λ _, 0) sin (λ _, 1) (λ _, 0) 0).
  destruct (H1 sin_bounds ltac:(auto_diff) ltac:(auto_diff) ltac:(auto)) as [g' [H6 H7]].
  assert (H8: ⟦ der 0 ⟧ sin = cos) by auto_diff.
  pose proof derivative_at_unique sin g' cos 0 H6 H8 as H9.
  rewrite cos_0, H7 in H9.
  lra.
Qed.