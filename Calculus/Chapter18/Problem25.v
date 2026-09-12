From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_25_i :
  ~ (∃ f, continuous f /\ ∀ x, ∫ 0 x f = exp x).
Abort.

(* The upper endpoint is x^2, so the equation determines f only on [0,infinity). *)
Lemma lemma_18_25_ii : ∀ f, continuous f ->
  ((∀ x, ∫ 0 (x^2) f = 1 - exp (2 * x^2)) <->
   (∀ t, 0 <= t -> f t = -2 * exp (2 * t))).
Abort.
