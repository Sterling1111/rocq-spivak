From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_30 : forall f a b,
  a < b ->
  ∫ a b (fun x => √(1 + (⟦ der ⟧ f x)^2)) >= b - a.
Admitted.
