From Calculus.Chapter23 Require Import Prelude.
Require Import Coq.Lists.List.

(* Problem 11: Kempner series and generalizations. *)

(* Represents the condition that 'd' does not appear in the base-10 digits of 'n' *)
Parameter digits_exclude : nat -> nat -> bool.

(* (a) Show that the sum of the reciprocals of the numbers in A (no 9) converges. *)
Lemma problem_23_11_a :
  exists S, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else if digits_exclude 9 n then 1 / INR n else 0) = S.
Abort.

(* (b) Sum of reciprocals of B (numbers not having all 10 digits) converges. *)
Parameter does_not_have_all_digits : nat -> bool.

Lemma problem_23_11_b :
  exists S, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else if does_not_have_all_digits n then 1 / INR n else 0) = S.
Abort.
