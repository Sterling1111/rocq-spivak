From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_7 : ∀ f,
  continuous f -> (∀ x y, f (x + y) = f x + f y) -> ∃ c, ∀ x, f x = c * x.
Proof. Admitted.
