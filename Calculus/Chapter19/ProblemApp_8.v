From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_App_8 : forall a,
  a > 0 ->
  ∫ (-a) a (fun x => 4 * (a^2 - x^2)) = 16 / 3 * a^3.
Abort.
