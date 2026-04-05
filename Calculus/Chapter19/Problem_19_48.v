From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_48 : forall f P,
  (forall x, x = 0 \/ x = 1 \/ x = 2 -> P x = f x) ->
  (exists A B C, forall x, P x = A * x^2 + B * x + C) ->
  ∫ 0 2 P = 1 / 3 * (f 0 + 4 * f 1 + f 2).
Admitted.
