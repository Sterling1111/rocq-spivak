From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_24 : ∀ f f' f'',
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ f' = f'' -> (∀ x, f'' x > 0) ->
  ∀ a x, x <> a -> f x > f a + f' a * (x-a).
Abort.
