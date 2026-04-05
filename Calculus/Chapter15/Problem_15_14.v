From Calculus.Chapter15 Require Import Prelude.

(* Problem 14: Sum-to-product formulas *)

(* (a) sin x + sin y *)
Lemma lemma_15_14_a : forall x y,
  sin x + sin y = 2 * sin ((x + y) / 2) * cos ((x - y) / 2).
Admitted.

(* (b) cos x + cos y *)
Lemma lemma_15_14_b : forall x y,
  cos x + cos y = 2 * cos ((x + y) / 2) * cos ((x - y) / 2).
Admitted.

(* cos x - cos y *)
Lemma lemma_15_14_c : forall x y,
  cos x - cos y = -2 * sin ((x + y) / 2) * sin ((x - y) / 2).
Admitted.
