From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_6 : forall x y,
  cos (x + y) = cos x * cos y - sin x * sin y.
Proof.
  intros x y.
  set (f := fun t => cos (t + y)).
  set (f' := fun t => - sin (t + y)).
  set (f'' := fun t => - cos (t + y)).
  pose proof theorem_4 f f' f'' (cos y) (- sin y) as H1.
  assert (⟦ der ⟧ f = f' /\ ⟦ der ⟧ f' = f'') as [H2 H3] by (unfold f, f'; split; auto_diff).
  specialize (H1 H2 H3).
  assert (forall t, f'' t + f t = 0) as H4 by (intro t; unfold f, f''; lra).
  specialize (H1 H4).
  assert (f 0 = cos y /\ f' 0 = - sin y) as [H5 H6]
  by (unfold f, f'; replace (0 + y) with y by lra; split; reflexivity).
  specialize (H1 H5 H6 x).
  unfold f in H1. rewrite H1. lra.
Qed.