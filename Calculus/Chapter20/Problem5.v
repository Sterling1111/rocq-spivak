From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_5 : forall f,
  (forall x, x <> 0 -> f x = (exp x - 1) / x) ->
  f 0 = 1 ->
  ⟦ Der 0 ⟧ f = 1 / 2.
Abort.
