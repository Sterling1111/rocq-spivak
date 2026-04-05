From Calculus.Chapter18 Require Import Prelude.

(* Problem 10: Show that F(x) = \int_2^x 1/\log t dt is not bounded on [2, \infty). *)
Lemma problem_18_10 : ~ (exists M, forall x, 2 <= x -> ∫ 2 x (fun t => 1 / log t) <= M). Admitted.
