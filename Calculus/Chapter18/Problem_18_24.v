From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_24 : forall x n,
  (n > 0)%nat -> exp x > x^n / INR (fact n).
Admitted.
