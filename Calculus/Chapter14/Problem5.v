From Calculus.Chapter14 Require Import Prelude.

(* Problem 5: Find a function g such that ... *)

(* (i) ∫ 0 x (t * g(t)) dt = x + x^2 *)
Lemma lemma_14_5_i : exists g : R -> R,
  forall x, ∫ 0 x (fun t => t * g t) = x + x^2.
Abort.

(* (ii) ∫ 0 (x^2) (t * g(t)) dt = x + x^2 *)
Lemma lemma_14_5_ii : exists g : R -> R,
  forall x, ∫ 0 (x^2) (fun t => t * g t) = x + x^2.
Abort.
