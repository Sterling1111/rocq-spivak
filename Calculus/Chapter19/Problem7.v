From Calculus.Chapter19 Require Import Prelude.

(* Problem 7: Find ∫ dx / √(x^n - x^2). *)

Lemma lemma_19_7 : forall n c,
  (n > 2)%nat ->
  ∫ (λ x, 1 / √(x ^ n - x ^ 2)) (0, ∞) =
    (λ x, -2 / (INR n - 2) * √(1 / x ^(n - 2) - 1) + c).
Abort.
