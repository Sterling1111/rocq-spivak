From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_App_3 : forall a b,
  a > 0 -> b > 0 ->
  π * ∫ (-a) a (fun x => b^2 * (1 - x^2 / a^2)) = 4 / 3 * π * a * b^2.
Admitted.
