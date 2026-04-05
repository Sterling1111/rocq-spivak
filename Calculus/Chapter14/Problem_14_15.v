From Calculus.Chapter14 Require Import Prelude.

(* Problem 15: Bisecting curves *)

(* (a) If C1 is the graph of f(x) = x^2, x ≥ 0, and C is the graph of f(x) = 2x^2, x ≥ 0,
   find C2 so that C bisects C1 and C2. *)
Lemma lemma_14_15_a : exists g : R -> R,
  (forall x, x >= 0 ->
    ∫ (x^2) (2*x^2) (fun t => 1) * x =
    ∫ 0 x (fun t => 2*t^2 - g t)).
Admitted.

(* (b) More generally, find C2 if C1 is the graph of f(x) = x^m
   and C is the graph of f(x) = c*x^m for some c > 1. *)
Lemma lemma_14_15_b : forall (m : nat) (c : R),
  c > 1 ->
  exists g : R -> R,
  forall x, x >= 0 ->
    ∫ (x ^ m) (c * x ^ m) (fun t => 1) * x =
    ∫ 0 x (fun t => c * t ^ m - g t).
Admitted.
