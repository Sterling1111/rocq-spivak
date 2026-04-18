From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_27 : forall f a b,
  a < b ->
  ∫ a b (fun theta => (f theta)^2 / 2) >= 0.
Abort.
