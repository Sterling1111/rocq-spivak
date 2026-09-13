From Calculus.Chapter14 Require Import Prelude.

Lemma lemma_14_14 : ∀ f a b n,
  (n > 0)%nat ->
  a < b ->
  continuous_on f [a, b] ->
  (∀ x, x ∈ [a, b] -> f x >= 0) ->
  ∫ a b (λ x, (f x) ^ n) = 0 ->
  ∀ x, x ∈ [a, b] -> f x = 0.
Abort.
