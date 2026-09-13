From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_34 : ∀ f f' a b, a < b ->
  derivative_on f f' [a,b] -> continuous_on f' [a,b] ->
  limit_pinf (λ k, ∫ a b (λ t, f t*sin (k*t))) 0.
Abort.
