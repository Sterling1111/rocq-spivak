From Calculus.Chapter19 Require Import Prelude.

(* Problem 8: Potpourri. (No holds barred.) *)

Lemma lemma_19_8_i : forall c,
  ∫ (λ x, log (log x) / x) (1, ∞) = (λ x, (log (log x))^2 / 2 + c).
Abort.

Lemma lemma_19_8_ii : forall c,
  ∫ (λ x, x * exp (-x^2)) = (λ x, -exp (-x^2) / 2 + c).
Abort.

Lemma lemma_19_8_iii : forall c,
  ∫ (λ x, arctan x / (1 + x^2)) = (λ x, (arctan x)^2 / 2 + c).
Abort.
