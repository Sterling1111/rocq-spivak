From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_18 : forall x y,
  x > 0 -> y > 0 -> log (x * y) = log x + log y.
Abort.
