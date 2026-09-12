From Calculus.Chapter20 Require Import Prelude.

From Calculus.Chapter20 Require Import Problem23.

Lemma lemma_20_27_a : ∀ f a b,
  a < b -> continuous_on f [a,b] -> f a = f b ->
  (∀ x, a < x < b -> schwarz_second_derivative f x 0) ->
  ∀ x, a <= x <= b -> f x = f a.
Abort.
Lemma lemma_20_27_b : ∀ f a b,
  a < b -> continuous_on f [a,b] ->
  (∀ x, a < x < b -> schwarz_second_derivative f x 0) ->
  ∀ x, a <= x <= b -> f x = f a + (f b - f a) / (b-a) * (x-a).
Abort.
