From Calculus.Chapter23 Require Import Prelude.

(* Problem 1: Decide whether each of the following infinite series is convergent or divergent. *)

Lemma problem_23_1_example1 : forall θ,
  exists S, ∑ 0 ∞ (fun n => sin (INR n * θ) / INR (n^2)) = S.
Admitted.

Lemma problem_23_1_example2 :
  exists S, ∑ 0 ∞ (fun n => (-1)^n * (log (INR n) / INR n)) = S.
Admitted.
