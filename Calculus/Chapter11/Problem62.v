From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_62 : forall f a,
  continuous_at f a ->
  differentiable_at (λ x, |f x|) a ->
  differentiable_at f a.
Proof.
  intros f a H1 H2.
  destruct (Rtotal_order (f a ) 0) as [H3 | [H3 | H3]].
  - apply differentiable_at_eq with (f1 := fun x => -1 * |f x|).
    { 
      pose proof continuous_at_locally_neg f a H1 H3 as [δ [H4 H5]].
      exists δ; split; auto.
      intros x H6.
      specialize (H5 x H6).
      solve_R.
    }
    apply differentiable_at_mult_const_l; auto.
  - assert (minimum_point (λ x : ℝ, |(f x)|) (a - 1, a + 1) a) as H4 by (split; solve_R).
    pose proof derivative_at_minimum_point_zero (λ x, |(f x)|) (a - 1) (a + 1) a H4 H2 as H5.
    unfold derivative_at, differentiable_at in *.
    exists 0.
    intros ε H6.
    specialize (H5 ε H6) as [δ [H7 H8]].
    exists δ.
    split; auto.
    intros x H9.
    specialize (H8 x H9).
    rewrite H3, Rabs_R0, Rminus_0_r, Rminus_0_r, Rabs_div in *.
    rewrite Rabs_Rabsolu in H8.
    exact H8.
  - apply differentiable_at_eq with (f1 := λ x, |f x|); auto.
    pose proof continuous_at_locally_pos f a H1 H3 as [δ [H4 H5]].
    exists δ. split; auto.
    intros x H6. specialize (H5 x H6).
    solve_R.
Qed.