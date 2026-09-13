From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_27 : ∀ f a b ε,
  a < b -> integrable_on a b f -> ε > 0 ->
  ∃ g h, continuous_on g [a, b] /\ continuous_on h [a, b] /\
    (∀ x, x ∈ [a, b] -> g x <= f x <= h x) /\
    ∫ a b h - ∫ a b g < ε.
Abort.
