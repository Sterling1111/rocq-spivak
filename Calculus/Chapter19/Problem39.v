From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_39 : ∀ u v u' v' a L I,
  derivative_on u u' [a,∞) -> derivative_on v v' [a,∞) ->
  continuous_on u' [a,∞) -> continuous_on v' [a,∞) ->
  limit_pinf (λ x, u x*v x) L ->
  improper_integral_pinf a (λ x, u x*v' x) I ->
  improper_integral_pinf a (λ x, u' x*v x) (L-u a*v a-I).
Abort.
