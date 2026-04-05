From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_App_6 : forall f a b,
  a < b ->
  2 * π * ∫ a b (fun x => x * f x) >= 0.
Admitted.
