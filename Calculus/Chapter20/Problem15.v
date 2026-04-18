From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_15 : forall x,
  x > 1 ->
  ~ exists L, limit_at_infinity (fun n => P(n, 0, log) x) L.
Abort.
