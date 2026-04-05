From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_46 : forall a b,
  a > 0 -> b > 0 ->
  limit_at_infinity (fun x => ((a^x + b^x)/2)^(1/x)) (sqrt (a * b)).
Admitted.
