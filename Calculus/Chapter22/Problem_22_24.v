From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_24_a : forall f,
  differentiable f ->
  (forall x, Rabs (⟦ der ⟧ f x) < 1) ->
  forall x y, f x = x -> f y = y -> x = y.
Admitted.

Lemma lemma_22_24_b : forall f c,
  differentiable f ->
  c < 1 ->
  (forall x, Rabs (⟦ der ⟧ f x) <= c) ->
  exists x, f x = x.
Admitted.

Lemma lemma_22_24_c : exists f,
  differentiable f /\ (forall x, Rabs (⟦ der ⟧ f x) <= 1) /\ (forall x, f x <> x).
Admitted.
