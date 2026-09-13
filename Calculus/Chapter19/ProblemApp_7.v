From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_App_7 : ∀ f g a b, 0 <= a -> a < b ->
  continuous_on f [a,b] -> increasing_on f [a,b] -> 0 <= f a ->
  continuous_on g [f a,f b] -> (∀ x, a <= x <= b -> g (f x) = x) ->
  π*b*f b^2 - π*a*f a^2 - π * ∫ a b (λ x, f x^2) =
    2*π * ∫ (f a) (f b) (λ y, y*g y).
Abort.
