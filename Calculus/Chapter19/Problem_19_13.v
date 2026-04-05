From Calculus.Chapter19 Require Import Prelude.

(* Problem 13: Derive the formula for ∫ sec x dx in two ways. *)

Lemma lemma_19_13_a : forall c,
  ∫ (λ x, 1 / cos x) (-π/2, π/2) = (λ x, log (Rabs (1 / cos x + tan x)) + c).
Admitted.

Lemma lemma_19_13_b : forall c,
  ∫ (λ x, 1 / cos x) (-π/2, π/2) = (λ x, log (Rabs (tan (x / 2 + π / 4))) + c).
Admitted.
