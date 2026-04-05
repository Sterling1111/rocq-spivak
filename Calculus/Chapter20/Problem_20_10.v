From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_10 : forall x,
  P(3, 0, fun x => x^3 - cos x) x = -1 + x^2 / 2 + x^3.
Admitted.
