From Calculus.Chapter14 Require Import Prelude.

Lemma lemma_14_21 : ∀ f f',
  ⟦ der ⟧ f [0, 1] = f' ->
  f 0 = 0 ->
  integrable_on 0 1 (λ x, (f' x)^2) ->
  ∀ x, x ∈ [0, 1] ->
  |f x| <= √(∫ 0 1 (λ x, |f' x|^2)).
Abort.
