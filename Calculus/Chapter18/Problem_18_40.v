From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_40 : forall x,
  x > 0 -> exp x = 1 + x + x^2 / 2 + sum_f_R0 (fun k => x^k / INR (fact k)) 3.
Admitted.
