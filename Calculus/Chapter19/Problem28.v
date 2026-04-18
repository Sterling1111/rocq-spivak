From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_28 : forall f g theta0 theta1,
  theta0 < theta1 ->
  (forall theta, theta0 <= theta <= theta1 -> (f theta)^2 / 2 = g theta) ->
  ∫ theta0 theta1 (fun theta => (f theta)^2 / 2) = ∫ theta0 theta1 g.
Abort.
