From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_28_b : forall fn f a b,
  (forall n, continuous_on (fn n) (fun x => a <= x <= b)) ->
  continuous_on f (fun x => a <= x <= b) ->
  (forall n x, a <= x <= b -> fn (S n) x <= fn n x) ->
  pointwise_limit fn f (fun x => a <= x <= b) ->
  uniform_limit fn f (fun x => a <= x <= b).
Abort.
