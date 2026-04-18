From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_34 : forall f a b,
  a < b ->
  continuous_on (⟦ der ⟧ f) [a, b] ->
  limit_at_infinity (fun lambda => ∫ a b (fun t => f t * sin (lambda * t))) 0.
Abort.
