From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_41 : ∀ f,
  f 0 = 0 -> (∀ x, x <> 0 -> f x = exp (-1 / x^2) * sin (1/x)) ->
  ∀ k : nat, ⟦ der ^ k 0 ⟧ f = (λ _, 0).
Abort.
