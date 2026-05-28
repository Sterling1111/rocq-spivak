From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_12 : ∀ f F,
  non_decreasing_on f [1, ∞) ->
  (∀ x, x >= 1 -> F x = ∫ 1 x (λ t, f t / t)) ->
  (bounded_on f [1, ∞)) <-> (bounded_on (F / log) [1, ∞)).
Proof.
Abort.
