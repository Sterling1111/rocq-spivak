From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_48 : forall x,
  x > 0 ->
  limit_at_infinity (fun n => n * (x^(1/n) - 1)) (log x).
Admitted.
