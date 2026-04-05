From Calculus.Chapter19 Require Import Prelude.

(* Problem 20: Prove that f(x) = e^x/(e^{5x} + e^x + 1) has an elementary primitive. *)

Lemma lemma_19_20 : exists F,
  differentiable F /\
  ⟦ der ⟧ F = (fun x => exp x / (exp (5*x) + exp x + 1)).
Admitted.
