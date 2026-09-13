From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_19 : ∀ f a b x0,
  a < b ->
  bounded_on f [a, b] ->
  x0 ∈ (a, b) ->
  (∀ x, x ∈ [a, b] -> x <> x0 -> ⟦ lim x ⟧ f [a, b] = f x) ->
  integrable_on a b f.
Abort.
