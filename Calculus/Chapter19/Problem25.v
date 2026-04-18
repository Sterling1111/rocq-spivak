From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_25 : forall r,
  r > 0 ->
  2 * ∫ (-r) r (fun x => √(r^2 - x^2)) = π * r^2.
Abort.
