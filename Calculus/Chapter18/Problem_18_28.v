From Calculus.Chapter18 Require Import Prelude.

(* Problem 28: (a) Prove that 1 + x + ... + x^n/n! <= e^x for x >= 0. *)
Lemma problem_18_28_a : forall x n, 0 <= x ->
  sum_f_R0 (fun i => x^i / INR (fact i)) n <= exp x. Admitted.
