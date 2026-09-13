From Calculus.Chapter22 Require Import Prelude Problem23.

Lemma lemma_22_24_a : ∀ f,
  differentiable f ->
  (∀ x, |(⟦ Der ⟧ f) x| < 1) ->
  ∀ x y, f x = x -> f y = y -> x = y.
Proof.
  intros f H1 H2.
  assert (H3 : ∀ x y, x < y -> f x = x -> f y = y -> False).
  {
    intros x y H3 H4 H5.
    destruct (mean_value_theorem f x y H3) as [t [H6 H7]].
    - apply continuous_imp_continuous_on. apply differentiable_imp_continuous. auto.
    - apply differentiable_imp_differentiable_on; auto.
      apply differentiable_domain_open. auto.
    - apply derivative_at_imp_derive_at in H7.
      specialize (H2 t). change (|⟦ Der t ⟧ f| < 1) in H2.
      rewrite H7, H4, H5 in H2.
      replace ((y-x)/(y-x)) with 1 in H2 by (field; lra). solve_R.
  }
  intros x y H4 H5. destruct (Rtotal_order x y) as [H6 | [H6 | H6]]; auto;
    exfalso; eapply H3; eauto.
Qed.

Lemma lemma_22_24_b : ∀ f c,
  differentiable f ->
  c < 1 ->
  (∀ x, |(⟦ Der ⟧ f) x| <= c) ->
  ∃ x, f x = x.
Proof.
  intros f c H1 H2 H3.
  assert (H4 : ∀ x y, x < y -> Rabs (f x-f y) <= c * Rabs (x-y)).
  {
    intros x y H4. destruct (mean_value_theorem f x y H4) as [t [H5 H6]].
    - apply continuous_imp_continuous_on. apply differentiable_imp_continuous. auto.
    - apply differentiable_imp_differentiable_on; auto.
      apply differentiable_domain_open. auto.
    - apply derivative_at_imp_derive_at in H6.
      specialize (H3 t). change (Rabs (⟦ Der t ⟧ f) <= c) in H3.
      rewrite H6, Rabs_div, (Rabs_right (y-x) ltac:(lra)) in H3.
      rewrite Rabs_minus_sym, (Rabs_left (x-y) ltac:(lra)).
      apply Rmult_le_compat_r with (r := y-x) in H3; [| lra].
      field_simplify in H3; nra.
  }
  destruct (lemma_22_23_c f c 0 H2) as [b [L H5]].
  - intros x y. destruct (Rtotal_order x y) as [H5 | [H5 | H5]].
    + apply H4. auto.
    + subst y. rewrite Rminus_diag, Rminus_diag, Rabs_R0. lra.
    + rewrite (Rabs_minus_sym (f x) (f y)), (Rabs_minus_sym x y). apply H4. auto.
  - exists L. tauto.
Qed.

Lemma lemma_22_24_c : ∃ f,
  differentiable f /\ (∀ x, |(⟦ Der ⟧ f) x| <= 1) /\ (∀ x, f x <> x).
Proof.
  exists (λ x, x+1).
  assert (H1 : ⟦ der ⟧ (λ x, x+1) = (λ _, 1)) by auto_diff.
  split.
  - apply derivative_imp_differentiable with (f' := λ _, 1). auto.
  - rewrite (derivative_imp_derive _ _ H1). split; intros x; solve_R.
Qed.
