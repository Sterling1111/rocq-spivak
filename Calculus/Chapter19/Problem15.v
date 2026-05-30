From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_15 : forall f f'',
  ⟦ der ^ 2 ⟧ f = f'' ->
  continuous f'' ->
  ∫ 0 π (λ x, (f x + f'' x) * sin x) = 2 ->
  f π = 1 ->
  f 0 = 1.
Proof.
  intros f f'' H1 H2 H3 H4.
  set (f' := ⟦ Der ⟧ f).
  assert (H5 : ⟦ der ⟧ f = f').
  { 
    apply derive_spec; auto. clear f'. destruct H1 as [f' [H1 _]].
    apply derivative_imp_differentiable with (f' := f'). apply nth_derivative_1 in H1; auto. 
  }
  assert (H6 : ⟦ der ⟧ f' = f'').
  {
    destruct H1 as [f1 [H1 H6]].
    apply nth_derivative_1 in H1.
    assert (f1 = f') by (eapply derivative_unique; eauto).
    subst; auto.
  }
  assert (H7 : ∫ (λ x : ℝ, (f x + f'' x) * sin x) = (λ x : ℝ, f' x * sin x - f x * cos x)) by auto_int.
  assert (H8 : ∫ 0 π (λ x : ℝ, (f x + f'' x) * sin x) = f π + f 0).
  {
    assert (H8 : continuous (λ x : ℝ, (f x + f'' x) * sin x)).
    {
      pose proof differentiable_imp_continuous f ltac:(eapply derivative_imp_differentiable; eauto) as H8.
      auto_cont.
    }
    pose proof definite_integral_eval_general (λ x : ℝ, (f x + f'' x) * sin x) (λ x : ℝ, f' x * sin x - f x * cos x) 0 π H8 as H9.
    rewrite H9.
    eval_math_constants.
    lra.
    auto.
  }
  lra.
Qed.

Lemma lemma_19_15' : forall f f' f'',
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ f' = f'' ->
  continuous f'' ->
  ∫ 0 π (λ x, (f x + f'' x) * sin x) = 2 ->
  f π = 1 ->
  f 0 = 1.
Proof.
  intros f f' f'' H1 H2 H3 H4 H5.
  assert (H7 : ∫ (λ x : ℝ, (f x + f'' x) * sin x) = (λ x : ℝ, f' x * sin x - f x * cos x)) by auto_int.
  assert (H8 : ∫ 0 π (λ x : ℝ, (f x + f'' x) * sin x) = f π + f 0).
  {
    assert (H8 : continuous (λ x : ℝ, (f x + f'' x) * sin x)).
    {
      pose proof differentiable_imp_continuous f ltac:(eapply derivative_imp_differentiable; eauto) as H8.
      auto_cont.
    }
    pose proof definite_integral_eval_general _ (λ x : ℝ, f' x * sin x - f x * cos x) 0 π H8 as H9.
    rewrite H9.
    eval_math_constants.
    lra.
    auto.
  }
  lra.
Qed.