From Calculus.Chapter15 Require Import Prelude.

(* Problem 22: Every point on the unit circle is of the form (cos θ, sin θ) *)
Lemma lemma_15_22 : forall x y,
  x^2 + y^2 = 1 ->
  exists θ, x = cos θ /\ y = sin θ.
Abort.
