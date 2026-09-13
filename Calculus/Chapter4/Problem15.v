From Calculus.Chapter4 Require Import Prelude.

(* Draw the graph, considering also a=0. Hint: Problem 1-18. *)
Definition problem_4_15 (a b c : ℝ) : Ensemble point :=
  graph (λ x, a*x^2+b*x+c).
