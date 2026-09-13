From Calculus.Chapter14 Require Import Prelude.

Lemma lemma_14_22 : ∀ f f',
  ⟦ der ⟧ f = f' ->
  f 0 = 0 ->
  (∀ x, 0 < f' x <= 1) ->
  ∀ x, x >= 0 ->
  ∫ 0 x (λ t, (f t)^3) <= (∫ 0 x f)^2.
Proof.
  intros f f' H1 H2 H3 x H4.
  assert (H5 : continuous f).
  { apply differentiable_imp_continuous. apply derivative_imp_differentiable with (f' := f'). auto. }
  set (F := λ t, ∫ 0 t f).
  assert (H6 : ⟦ der ⟧ F = f) by (unfold F; apply FTC1_global; auto).
  assert (H7 : F 0 = 0) by (unfold F; apply integral_n_n).
  assert (H8 : ∀ t, 0 <= t -> 0 <= f t).
  {
    intros t H8.
    pose proof derivative_nonneg_imp_nondecreasing f f' H1
      ltac:(intros u; specialize (H3 u); lra) as H9.
    specialize (H9 0 t ltac:(apply Full_intro) ltac:(apply Full_intro) H8).
    rewrite H2 in H9. lra.
  }
  destruct (Req_dec x 0) as [H9 | H9].
  - subst. rewrite !integral_n_n. lra.
  - assert (H10 : ⟦ der ⟧ (λ t, 2 * F t - (f t)^2) [0, x] =
      (λ t, 2 * f t * (1 - f' t))) by auto_diff.
    assert (H11 : ∀ t, t ∈ [0, x] -> (f t)^2 <= 2 * F t).
    {
      intros t H11.
      pose proof derivative_on_nonneg_imp_nondecreasing_on _ _ 0 x ltac:(lra) H10
        ltac:(intros u H12; specialize (H3 u); specialize (H8 u ltac:(solve_R)); nra) as H12.
      specialize (H12 0 t ltac:(solve_R) H11 ltac:(solve_R)).
      cbn beta in H12.
      rewrite H2, H7 in H12. nra.
    }
    set (G := λ t, ∫ 0 t (λ u, (f u)^3)).
    assert (H12 : ⟦ der ⟧ G = (λ t, (f t)^3)).
    { unfold G. apply FTC1_global. auto_cont. }
    assert (H13 : ⟦ der ⟧ (λ t, (F t)^2 - G t) [0, x] =
      (λ t, 2 * F t * f t - (f t)^3)) by auto_diff.
    pose proof derivative_on_nonneg_imp_nondecreasing_on _ _ 0 x ltac:(lra) H13
      ltac:(intros t H14; specialize (H11 t H14); specialize (H8 t ltac:(solve_R)); nra) as H14.
    specialize (H14 0 x ltac:(solve_R) ltac:(solve_R) ltac:(lra)).
    cbn beta in H14.
    rewrite H7 in H14. unfold G in H14. rewrite integral_n_n in H14.
    unfold F in H14. nra.
Qed.
