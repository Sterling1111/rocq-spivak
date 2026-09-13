From Calculus.Chapter19 Require Import Prelude.

(* Problem 19: Express ∫ x^2 e^{-x^2} dx in terms of ∫ e^{-x^2} dx. *)

Lemma lemma_19_19 : ∀ c,
  ∫ (λ x, x^2 * exp (-x^2)) =
    (λ x, -x * exp (-x^2) / 2 + ∫ 0 x (λ t, exp (-t^2)) / 2 + c).
Abort.
