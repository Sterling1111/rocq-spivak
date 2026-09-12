From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_44_a : ∀ f f',
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ f' = f ->
  ∀ x, f x = (f 0 + f' 0)/2 * exp x + (f 0 - f' 0)/2 * exp (-x).
Abort.

Lemma lemma_18_44_b : ∀ f f',
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ f' = f ->
  ∀ x, f x = f' 0 * sinh x + f 0 * cosh x.
Abort.
