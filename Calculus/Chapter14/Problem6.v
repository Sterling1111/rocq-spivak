From Calculus.Chapter14 Require Import Prelude.

Lemma lemma_14_6_a : ∀ f C,
  C <> 0 ->
  continuous f ->
  (∀ x, ∫ 0 x f = (f x)^2 + C) ->
  ∃ c, (∀ x, f x = x / 2 + c) /\ C = - c^2.
Abort.

Lemma lemma_14_6_b : ∀ C,
  C <> 0 -> ∃ f b,
  b > 0 /\
  continuous f /\
  (∀ x, x <= b -> f x = 0) /\
  (∀ x, x > b -> f x <> 0) /\
  (∀ x, ∫ 0 x f = (f x)^2 + C).
Abort.

Lemma lemma_14_6_c : ∀ a b,
  a < 0 < b -> ∃ f,
  continuous f /\
  (∀ x, a <= x <= b -> f x = 0) /\
  (∀ x, x < a \/ x > b -> f x <> 0) /\
  (∀ x, ∫ 0 x f = (f x)^2).
Abort.
