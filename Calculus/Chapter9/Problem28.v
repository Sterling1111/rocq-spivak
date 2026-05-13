From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_28 : forall f g,
  (forall x, f x = x * g x) -> 
  continuous_at g 0 -> 
  differentiable_at f 0 /\ ⟦ der 0 ⟧ f = g.
Proof.
  intros f g H1 H2.
  assert (⟦ der 0 ⟧ f = g) as H3.
  {
    intros ε H3.
    destruct (H2 ε H3) as [δ [H4 H5]].
    exists δ; split; auto.
    intros x H6.
    simp_zero.
    specialize (H5 x H6).
    replace ((f x - f 0) / x - g 0) with (g x - g 0).
    2 : { do 2 rewrite H1. solve_R. }
    exact H5.
  }
  split; auto.
  apply derivative_at_imp_differentiable_at with (f' := g); auto.
Qed.