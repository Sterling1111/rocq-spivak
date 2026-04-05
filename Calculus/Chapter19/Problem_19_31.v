From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_31 : forall f a b,
  a < b ->
  ∫ a b (fun theta => √((f theta)^2 + (⟦ der ⟧ f theta)^2)) >= 0.
Admitted.
