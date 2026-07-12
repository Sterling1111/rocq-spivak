From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_24 : ∀ f,
  integrable f ->
  (∀ x, f x = ∫ 0 x f) -> f = λ _, 0.
Proof.
  intros f H1 H2.
  extensionality x.
  destruct (Rtotal_order 0 x) as [H3 | [H3 | H3]].
  - pose proof theorem_13_8 f 0 x ltac:(lra) ltac:(apply H1) as H4. 

    assert (H5 : f 0 = 0).
    { rewrite H2. apply integral_n_n. }

    assert (H6 : continuous_on f [0, x]).
    { replace f with (λ x, ∫ 0 x f); auto. extensionality y. auto. }

    assert (H7 : ⟦ der ⟧ f [0, x] = f).
    {
      pose proof FTC1 f 0 x H3 H6 as H7.
      replace (λ x : ℝ, ∫ 0 x f) with f in H7 by (extensionality y; auto); auto.
    }
    assert (H8 : ⟦ der ⟧ (λ t, f t * exp (- t)) [0, x] = (λ _, 0)).
    {
      apply derivative_on_eq with (f1 := f ⋅ (λ t, exp (- t))).
      - intros t H8. reflexivity.
      - apply derivative_on_ext with (f1' := (λ t, f t * exp (- t) + f t * - exp (- t))).
        + intros t H8. lra.
        + apply derivative_on_mult with (f' := f) (g' := λ t, - exp (- t)).
          * apply differentiable_domain_closed. lra.
          * exact H7.
          * auto_diff.
    }
    pose proof derivative_zero_imp_const (λ t, f t * exp (- t)) 0 x H3 H8 as [c H9].
    specialize (H9 x ltac:(solve_R)) as H10.
    specialize (H9 0 ltac:(solve_R)) as H11.
    rewrite Ropp_0, exp_0, H5, Rmult_0_l in H11.
    subst.
    pose proof exp_pos (- x) as H12.
    nra.
  - subst. rewrite H2, integral_n_n. reflexivity.
  - pose proof theorem_13_8 f x 0 ltac:(lra) ltac:(apply H1) as H4.
    assert (H5 : f 0 = 0).
    { rewrite H2. apply integral_n_n. }
    assert (H6 : continuous_on f [x, 0]).
    { 
      replace f with (λ y, ∫ 0 y f) by (extensionality y; auto).
      replace (λ y : ℝ, ∫ 0 y f) with ((λ _ : ℝ, ∫ 0 x f) + (λ y : ℝ, ∫ x y f))%function.
      2 : { extensionality y. rewrite (integral_split' f 0 y x); auto. }
      apply continuous_on_plus; auto_cont.
    }
    assert (H7 : ⟦ der ⟧ f [x, 0] = f).
    {
      pose proof FTC1' f x 0 H3 H6 as H8.
      replace (λ x : ℝ, ∫ x 0 f) with (-f)%function in H8.
      apply derivative_on_neg_iff in H8; auto.
      - apply differentiable_domain_closed; lra.
      - extensionality y; rewrite H2, <- integral_b_a_neg; auto.
    }
    assert (H8 : ⟦ der ⟧ (λ t, f t * exp (- t)) [x, 0] = (λ _, 0)).
    {
      apply derivative_on_eq with (f1 := f ⋅ (λ t, exp (- t))).
      - intros t H8'. reflexivity.
      - apply derivative_on_ext with (f1' := (λ t, f t * exp (- t) + f t * - exp (- t))).
        + intros t H8'. lra.
        + apply derivative_on_mult with (f' := f) (g' := λ t, - exp (- t)).
          * apply differentiable_domain_closed. lra.
          * exact H7.
          * auto_diff.
    }
    pose proof derivative_zero_imp_const (λ t, f t * exp (- t)) x 0 H3 H8 as [c H9].
    specialize (H9 x ltac:(solve_R)) as H10.
    specialize (H9 0 ltac:(solve_R)) as H11.
    rewrite Ropp_0, exp_0, H5, Rmult_0_l in H11.
    subst.
    pose proof exp_pos (- x) as H12.
    nra.
Qed.