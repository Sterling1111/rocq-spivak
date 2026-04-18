From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_30 : forall x y,
  x > 0 -> y > 0 -> log x / log y = log y / log x -> x = y \/ x = 1/y.
Abort.
