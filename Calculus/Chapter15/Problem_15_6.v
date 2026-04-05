From Calculus.Chapter15 Require Import Prelude.

(* Problem 6: Prove the addition formula for cos. *)

Lemma lemma_15_6 : forall x y,
  cos (x + y) = cos x * cos y - sin x * sin y.
Admitted.
