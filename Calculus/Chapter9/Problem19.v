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
  (forall x, f x <= g x /\ g x <= h x) ->
  ⟦ der a ⟧ f = f' -> ⟦ der a ⟧ h = h' ->
  f' a = h' a ->
  exists g', ⟦ der a ⟧ g = g' /\ g' a = f' a).
Proof.
  intros H1.
  specialize (H1 (λ _, 0) (λ _, 0) (λ x, if Rle_dec 0 x then 1 else 0) (λ _, 2) (λ _, 0) 0
        ltac:(solve_R) ltac:(auto_diff) ltac:(auto_diff) ltac:(reflexivity)) as [g' [H2 H3]].
  
  specialize (H2 1 ltac:(lra)) as [δ [H4 H5]].

  rewrite H3 in H5.
  
  set (h := if Rle_dec (δ / 2) (1 / 2) then - (δ / 2) else - (1 / 2)).

  specialize (H5 h ltac:(unfold h; solve_R)).
  
  assert (H7 : (if Rle_dec 0 0 then 1 else 0) = 1) by solve_R.
  
  assert (H8 : (if Rle_dec 0 (0 + h) then 1 else 0) = 0).
  { unfold h; solve_R. }
  
  rewrite H7, H8 in H5.
  
  assert (H9 : h <> 0) by solve_R.
  
  replace (((0 - 1) / h) - 0) with (-1 / h) in H5 by solve_R.
  rewrite Rabs_div in H5 by exact H9.
  replace (|(-1)|) with 1 in H5 by solve_abs.
  apply Rmult_lt_compat_r with (r := |h|) in H5; field_simplify in H5; unfold h in *; solve_R.
Qed.