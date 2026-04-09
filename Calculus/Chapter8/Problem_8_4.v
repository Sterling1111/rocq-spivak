From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_4_a : ∀ f a b x0,
  continuous_on f [a, b] ->
  f a = f b = 0 ->
  x0 ∈ [a, b] ->
  f x0 > 0 ->
  ∃ c d, a <= c < x0 < d <= b /\
  f c = f d = 0 /\ ∀ x, x ∈ (c, d) -> f x > 0.
Proof.
Admitted.

Lemma lemma_8_4_b : ∀ f a b,
  continuous_on f [a, b] ->
  a < b ->
  f a < f b ->
  ∃ c d, a <= c < d <= b ->
  f c = f a /\ f d = f b /\
  ∀ x, c < x < d -> f a < f x < f b.
Proof. 
Admitted.