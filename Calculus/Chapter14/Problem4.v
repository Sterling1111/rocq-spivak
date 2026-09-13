From Calculus.Chapter14 Require Import Prelude.
From Lib Require Import StdlibCompat.

Lemma lemma_14_4_i : ∀ f f_inv,
  (∀ x, f x = ∫ 0 x (λ t, 1 + sin (sin t))) ->
  inverse f f_inv ->
  ⟦ Der 0 ⟧ f_inv = 1.
Proof.
  intros f f_inv H1 H2.
  assert (H3 : ⟦ der ⟧ f = (λ x, 1 + sin (sin x))).
  {
    replace f with (λ x, ∫ 0 x (λ t, 1 + sin (sin t)))
      by (extensionality x; auto).
    apply FTC1_global. auto_cont.
  }
  assert (H4 : ∀ x, 1 + sin (sin x) <> 0).
  {
    intros x. pose proof sin_bounds x as H4.
    assert (H5 : -1 < sin (sin x)).
    { rewrite sin_compat in *. interval. }
    lra.
  }
  pose proof global_inverse_theorem f f_inv _ H2 H3 H4 as H5.
  assert (H6 : f_inv 0 = 0).
  {
    pose proof (proj1 (inverse_spec f f_inv H2) 0) as H6.
    rewrite H1, integral_n_n in H6. auto.
  }
  rewrite (derivative_at_imp_derive_at _ _ 0 (H5 0)), H6, sin_0, sin_0.
  lra.
Qed.

Lemma lemma_14_4_ii : ∀ f f_inv,
  (∀ x, f x = ∫ 1 x (λ t, cos (cos t))) ->
  inverse f f_inv ->
  ⟦ Der 0 ⟧ f_inv = 1 / cos (cos 1).
Proof.
  intros f f_inv H1 H2.
  assert (H3 : ⟦ der ⟧ f = (λ x, cos (cos x))).
  {
    replace f with (λ x, ∫ 1 x (λ t, cos (cos t)))
      by (extensionality x; auto).
    apply FTC1_global. auto_cont.
  }
  assert (H4 : ∀ x, cos (cos x) <> 0).
  {
    intros x. pose proof cos_bounds x as H4.
    assert (H5 : 0 < cos (cos x)).
    { rewrite cos_compat in *. interval. }
    lra.
  }
  pose proof global_inverse_theorem f f_inv _ H2 H3 H4 as H5.
  assert (H6 : f_inv 0 = 1).
  {
    pose proof (proj1 (inverse_spec f f_inv H2) 1) as H6.
    rewrite H1, integral_n_n in H6. auto.
  }
  rewrite (derivative_at_imp_derive_at _ _ 0 (H5 0)), H6.
  lra.
Qed.
