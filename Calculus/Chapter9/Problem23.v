From Calculus.Chapter9 Require Import Prelude.

Lemma problem_9_23 : ∀ f f',
  even f ->
  ⟦ der ⟧ f = f' ->
  ∀ x, f' x = - f' (- x).
Proof.
  intros f f' H1 H2 x.
  set (g := λ x, f (-x)).
  set (g' := λ x, - f' (-x)).
  assert (H3 : ⟦ der ⟧ g = g') by (unfold g, g'; auto_diff).
  assert (H4 : g = f) by (extensionality y; unfold g; auto).
  rewrite H4 in H3.
  pose proof derivative_unique f f' g' H2 H3 as H5.
  replace (f' x) with (g' x) by (rewrite H5; reflexivity).
  unfold g'.
  reflexivity.
Qed. 