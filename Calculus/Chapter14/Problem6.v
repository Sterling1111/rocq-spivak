From Calculus.Chapter14 Require Import Prelude.

(* Problem 6: Find all continuous functions f satisfying ∫ 0 x f = (f(x))^2 + C
   for some constant C ≠ 0, assuming f has at most one zero. *)

(* (a) Find all such f with at most one zero *)
Lemma lemma_14_6_a : forall f C,
  C <> 0 ->
  continuous f ->
  (forall x, ∫ 0 x f = (f x)^2 + C) ->
  exists c, (forall x, f x = x / 2 + c) /\ C = - c^2.
Abort.

(* (b) Find a solution that is 0 on (-∞, b] with 0 < b, but non-zero for x > b *)
Lemma lemma_14_6_b : forall C,
  C <> 0 -> exists f b,
  b > 0 /\
  continuous f /\
  (forall x, x <= b -> f x = 0) /\
  (forall x, x > b -> f x <> 0) /\
  (forall x, ∫ 0 x f = (f x)^2 + C).
Abort.

(* (c) For C = 0 and any interval [a, b] with a < 0 < b, find a solution
   that is 0 on [a, b] but non-zero elsewhere *)
Lemma lemma_14_6_c : forall a b,
  a < 0 < b -> exists f,
  continuous f /\
  (forall x, a <= x <= b -> f x = 0) /\
  (forall x, x < a \/ x > b -> f x <> 0) /\
  (forall x, ∫ 0 x f = (f x)^2).
Abort.
