From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_31_a : forall f a b,
  continuous_on f (cc a b) ->
  bounded_above (fun y => exists x, Rcc a b x /\ f x = y).
Abort.

Lemma lemma_22_31_b : forall f a b,
  continuous_on f (cc a b) ->
  uniformly_continuous_on f (cc a b).
Abort.
