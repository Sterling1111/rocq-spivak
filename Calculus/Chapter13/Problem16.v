From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_16 : ∀ f a b c,
  a < b ->
  integrable_on (Rmin (c * a) (c * b)) (Rmax (c * a) (c * b)) f ->
  ∫ (c * a) (c * b) f = c * ∫ a b (λ t, f (c * t)).
Abort.
