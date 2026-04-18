From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_12 : forall n x,
  (forall t, t <> 0 -> P(2 * n, 0, fun y => sin y / y) t = sum_f_R0 (fun k => (-1)^k / INR (fact (2 * k + 1)) * t^(2 * k)) n) ->
  False.
Abort.
