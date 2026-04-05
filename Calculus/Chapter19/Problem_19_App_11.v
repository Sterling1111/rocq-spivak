From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_App_11 : forall r,
  r > 0 ->
  2 * π * ∫ (-r) r (fun x => √(r^2 - x^2) * √(1 + (-x / √(r^2 - x^2))^2)) = 4 * π * r^2.
Admitted.
