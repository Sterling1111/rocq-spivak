From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_App_5 : forall a,
  a > 0 ->
  π * ∫ (-a * √3) (a * √3) (fun x => ((2*a)^2 - x^2) - a^2) = 4 * π * a^3 * √3.
Admitted.
