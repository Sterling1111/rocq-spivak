From Calculus.Chapter15 Require Import Prelude.

(* Problem 9 *)

(* (a) tan(x + y) = (tan x + tan y) / (1 - tan x * tan y) *)
Lemma lemma_15_9_a : forall x y,
  cos x <> 0 -> cos y <> 0 -> cos (x + y) <> 0 ->
  tan (x + y) = (tan x + tan y) / (1 - tan x * tan y).
Abort.

(* (b) arctan x + arctan y = arctan((x + y) / (1 - x * y)) *)
Lemma lemma_15_9_b : forall x y,
  x * y < 1 ->
  arctan x + arctan y = arctan ((x + y) / (1 - x * y)).
Abort.
