From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_14 : ∀ f a b c,
  a < b ->
  integrable_on a b f ->
  ∫ a b f = ∫ (a + c) (b + c) (λ x, f (x - c)).
Abort.
