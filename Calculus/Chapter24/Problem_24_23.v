From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_23_a : forall fn f a b,
  (forall n x, a <= x <= b -> exists M, Rabs (fn n x) <= M) ->
  uniform_limit fn f (fun x => a <= x <= b) ->
  exists M, forall x, a <= x <= b -> Rabs (f x) <= M.
Admitted.

Lemma lemma_24_23_b : exists fn f a b,
  (forall n, continuous_on (fn n) (fun x => a <= x <= b)) /\ pointwise_limit fn f (fun x => a <= x <= b) /\ ~ exists M, forall x, a <= x <= b -> Rabs (f x) <= M.
Admitted.
