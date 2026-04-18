From Calculus.Chapter19 Require Import Prelude.

(* Problem 10: Find the following integrals. *)

Lemma lemma_19_10_i : forall c,
  ∫ (λ x, exp x * sin x) = (λ x, exp x * (sin x - cos x) / 2 + c).
Abort.

Lemma lemma_19_10_ii : forall c,
  ∫ (λ x, exp x * cos x) = (λ x, exp x * (sin x + cos x) / 2 + c).
Abort.
