From Calculus.Chapter14 Require Import Prelude.

(* Problem 11: Find a function f such that f''(x) = 1/√(1 + (sin x)^2). *)

Lemma lemma_14_11 : exists f : R -> R,
  ⟦ der^2 ⟧ f = (fun x => 1 / √(1 + (sin x)^2)).
Admitted.
