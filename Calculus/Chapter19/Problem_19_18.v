From Calculus.Chapter19 Require Import Prelude.

(* Problem 18: Express ∫ log(log x) dx in terms of ∫ (log x)^{-1} dx. *)

Lemma lemma_19_18 : forall c,
  ∫ (λ x, log (log x)) (1, ∞) =
    (λ x, x * log (log x) - ∫ 1 x (fun t => 1 / log t) + c).
Admitted.
