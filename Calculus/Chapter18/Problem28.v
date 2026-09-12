From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_28_a : ∀ f g a b C,
  a < b -> continuous_on f [a,b] -> continuous_on g [a,b] ->
  (∀ x, x ∈ [a,b] -> 0 <= g x) ->
  (∀ x, x ∈ [a,b] -> f x <= C + ∫ a x (λ t, f t * g t)) ->
  ∀ x, x ∈ [a,b] -> f x <= C * exp (∫ a x g).
Abort.

Lemma lemma_18_28_b : ∀ f g,
  continuous g -> (∀ x, 0 <= f x) -> (∀ x, 0 <= g x) ->
  ⟦ der ⟧ f = (λ x, g x * f x) -> f 0 = 0 -> f = (λ _, 0).
Abort.
