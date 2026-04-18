From Calculus.Chapter19 Require Import Prelude.

(* Problem 12: The world's sneakiest substitution is t = tan(x/2). *)

Lemma lemma_19_12_a : forall x,
  x <> 0 ->
  sin x = 2 * tan (x / 2) / (1 + (tan (x / 2))^2).
Abort.

Lemma lemma_19_12_b : forall x,
  cos x = (1 - (tan (x / 2))^2) / (1 + (tan (x / 2))^2).
Abort.

Lemma lemma_19_12_c : forall c,
  ∫ (λ x, 1 / (1 + sin x + cos x)) = (λ x, log (Rabs (1 + tan (x / 2))) + c).
Abort.
