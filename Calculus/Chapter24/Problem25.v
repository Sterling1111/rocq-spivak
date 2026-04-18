From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_25 : exists fn f a b,
  (forall n, integrable_on a b (fn n)) /\ (forall x, rational x -> f x = 1) /\ (forall x, irrational x -> f x = 0) /\ pointwise_limit fn f (fun x => a <= x <= b).
Abort.
