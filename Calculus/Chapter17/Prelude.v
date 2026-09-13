From Calculus.Chapter4 Require Export Prelude.
From Lib Require Export Sets Functions Limit Continuity Interval Notations Reals_util Tactics.
Export FunctionNotations LimitNotations DerivativeNotations IntegralNotations
  IntervalNotations SetNotations.
Open Scope R_scope.

(** Two-sided calculus on an open time interval. No endpoint smoothness or
    global continuation of an orbit is assumed. *)
Definition scalar_derivative_on (l u : ℝ) (f f' : ℝ → ℝ) :=
  ∀ t, l < t < u → (⟦ der t ⟧ f = f').
Definition curve_derivative_on (l u : ℝ) (c v : vector_function 2) :=
  (⟦ der ⟧ c (λ t, l < t < u) = v)%vc.

Lemma scalar_constant l u f :
  (∀ τ, l < τ < u → ⟦ der τ ⟧ f = (λ _, 0)) →
  ∀ x y, l < x < u → l < y < u → f x = f y.
Proof.
  intros H1 x y H2 H3.
  assert (H4 : ∀ a b, l < a < u → l < b < u → a < b → f a = f b).
  { intros a b H5 H6 H7.
    assert (H8 : (⟦ der ⟧ f [a, b] = (λ _, 0))).
    { apply derivative_at_imp_derivative_on.
      - apply differentiable_domain_closed. exact H7.
      - intros t H9. apply H1. unfold Ensembles.In in H9. cbn in H9. lra. }
    destruct (derivative_zero_imp_const f a b H7 H8) as [k H10].
    rewrite (H10 a), (H10 b); unfold Ensembles.In; cbn; lra. }
  destruct (Rtotal_order x y) as [H11 | [-> | H11]]; auto.
  symmetry. apply H4; assumption.
Qed.

Lemma scalar_local_ext l u f g f' t :
  l < t < u → (∀ x, l < x < u → f x = g x) →
  (⟦ der t ⟧ f = f') → (⟦ der t ⟧ g = f').
Proof.
  intros H1 H2 H3. eapply derivative_at_eq; [|exact H3].
  exists (Rmin (t - l) (u - t)). split.
  - apply Rmin_pos; lra.
  - intros x H4. apply H2. apply Rabs_def2 in H4.
    pose proof (Rmin_l (t-l) (u-t)) as H5. pose proof (Rmin_r (t-l) (u-t)) as H6. lra.
Qed.

Lemma scalar_constant_derivative l u f k t :
  l < t < u → (∀ x, l < x < u → f x = k) →
  (⟦ der t ⟧ f = (λ _, 0)).
Proof.
  intros H1 H2. eapply scalar_local_ext with (f := λ _, k); eauto.
  - intros x H3. symmetry. auto.
  - apply derivative_at_const.
Qed.

Lemma scalar_sin_chain f f' t :
  (⟦ der t ⟧ f = f') →
  (⟦ der t ⟧ (λ x, sin (f x)) = (λ x, cos (f x) * f' x)).
Proof. intro H1. exact (derivative_at_comp f sin f' cos t H1 (derivative_sin (f t))). Qed.
Lemma scalar_cos_chain f f' t :
  (⟦ der t ⟧ f = f') →
  (⟦ der t ⟧ (λ x, cos (f x)) = (λ x, - sin (f x) * f' x)).
Proof. intro H1. exact (derivative_at_comp f cos f' (λ x, -sin x) t H1 (derivative_cos (f t))). Qed.

(** Infer the derivative using proved scalar rules; leave its algebraic
    simplification as an explicit, inspectable goal. *)
Ltac orbit_diff :=
  let d := open_constr:(_ : ℝ → ℝ) in
  match goal with |- ⟦ der ?t ⟧ ?f = _ =>
    let hyp := fresh "H1" in
    assert (hyp : (⟦ der t ⟧ f = d)) by
      (solve [eauto 14 using scalar_sin_chain, scalar_cos_chain
        with calculus_derivatives]);
    eapply derivative_at_ext_val; [exact hyp | cbn beta]
  end.
