From Calculus.Chapter19 Require Import Prelude.

(* Problem 23: Prove that \int_1^{\cosh x} \sqrt{t^2-1} dt = \frac{\cosh x \sinh x}{2} - \frac{x}{2}. *)
Lemma lemma_19_23 : ∀ x,
  x >= 0 ->
  ∫ 1 (cosh x) (λ t, √(t^2 - 1)) = (cosh x * sinh x) / 2 - x / 2.
Abort.
