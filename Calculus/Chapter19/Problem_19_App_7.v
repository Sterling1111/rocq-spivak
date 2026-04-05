From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_App_7 : forall f a b,
  a < b ->
  π * (f b)^2 * b - π * (f a)^2 * a = 2 * π * ∫ a b (fun y => y * f y) + π * ∫ a b (fun x => (f x)^2).
Admitted.
