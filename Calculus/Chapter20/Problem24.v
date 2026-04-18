From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_24 : forall f a,
  (forall x, f x >= 0) ->
  P(1, a, f) a = f a.
Abort.
