From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_18 : forall f a n x t,
  a < x -> a < t < x ->
  f x = P(n, a, f) x + ⟦ Der ^ (n + 1) t ⟧ f / INR (fact (n + 1)) * (x - a)^(n + 1) ->
  equal_up_to_order n f (P(n, a, f)) a.
Admitted.
