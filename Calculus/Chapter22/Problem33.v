From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_33 : forall f,
  (forall a, Rcc 0 1 a -> exists L, limit_at_point f a L) ->
  countable (fun a => Rcc 0 1 a /\ ~ continuous_at f a).
Abort.
