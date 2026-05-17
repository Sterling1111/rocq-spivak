From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_53 : forall g g' g'' f,
  g 0 = 0 ->
  g' 0 = 0 ->
  g'' 0 = 17 ->
  ⟦ der ⟧ g = g' ->
  ⟦ der ⟧ g' = g'' ->
  f 0 = 0 ->
  (forall x, x <> 0 -> f x = g x / x) ->
  ⟦ der 0 ⟧ f = (fun _ => 17 / 2).
Proof.
  intros g g' g'' f H1 H2 H3 H4 H5 H6 H7.
  apply limit_eq with (f1 := λ x, g x / x^2).
  - exists 1. split; [lra |].
    intros x H8.
    rewrite H6, Rminus_0_r, Rplus_0_l.
    rewrite H7; solve_R.
  - step_lhopital g' (λ x, 2 * x).
    + rewrite <- H1 at 2.
      apply differentiable_at_imp_continuous_at.
      apply derivative_at_imp_differentiable_at with (f' := g'); auto.
    + apply limit_eq with (f1 := λ x, 1 / 2 * ((g' x - g' 0) / (x - 0))).
      * exists 1. split; [lra |].
        intros x H8. solve_R.
      * replace (17 / 2) with (1 / 2 * 17) by lra.
        apply limit_mult.
        -- apply limit_const.
        -- rewrite <- H3.
           replace (λ x : ℝ, (g' x - g' 0) / (x - 0)) with (λ h : ℝ, (g' (0 + h) - g' 0) / h).
           2 : { extensionality h. simp_zero. reflexivity. }
           exact (H5 0).
Qed.