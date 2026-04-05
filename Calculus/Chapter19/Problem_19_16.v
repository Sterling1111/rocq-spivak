From Calculus.Chapter19 Require Import Prelude.

(* Problem 16: (a) Find ∫ arcsin x dx. (b) Find ∫ f^{-1}(x) dx in terms of ∫ f(x) dx. *)

Lemma lemma_19_16_a : forall c,
  ∫ (λ x, arcsin x) (-1, 1) = (λ x, x * arcsin x + √(1 - x^2) + c).
Admitted.

Lemma lemma_19_16_b : forall f f_inv F c,
  inverse f f_inv ->
  (forall x, ⟦ der ⟧ F x = f x) ->
  ∫ (λ x, f_inv x) = (λ x, x * f_inv x - F (f_inv x) + c).
Admitted.
