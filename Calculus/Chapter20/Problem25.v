From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_25 : ∀ f f',
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ f' = f -> f 0 = 0 -> f' 0 = 0 -> f = (λ _, 0).
Abort.
