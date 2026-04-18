From Calculus.Chapter15 Require Import Prelude.

(* Problem 17: If x = tan(u/2), express sin u and cos u in terms of x. *)

Lemma lemma_15_17_sin : forall u,
  cos (u / 2) <> 0 ->
  sin u = 2 * tan (u / 2) / (1 + (tan (u / 2))^2).
Abort.

Lemma lemma_15_17_cos : forall u,
  cos (u / 2) <> 0 ->
  cos u = (1 - (tan (u / 2))^2) / (1 + (tan (u / 2))^2).
Abort.
