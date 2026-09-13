From Calculus.Chapter14 Require Import Prelude.

Lemma lemma_14_17 : ∀ f a b,
  a < b ->
  continuous_on f [a, b] ->
  ∀ y, Rmin (f a) (f b) <= y <= Rmax (f a) (f b) ->
  ∃ c, c ∈ [a, b] /\ f c = y.
Abort.
