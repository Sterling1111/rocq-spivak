From Calculus.Chapter4 Require Import Prelude.

(* Sketch each graph. For (i), discuss x near zero and large |x|,
   its position relative to y=x, and why positive x suffices initially. *)

Definition problem_4_10_i : Ensemble point :=
  graph_on (λ x, x <> 0) (λ x, x+1/x).

Definition problem_4_10_ii : Ensemble point :=
  graph_on (λ x, x <> 0) (λ x, x-1/x).

Definition problem_4_10_iii : Ensemble point :=
  graph_on (λ x, x <> 0) (λ x, x^2+1/x^2).

Definition problem_4_10_iv : Ensemble point :=
  graph_on (λ x, x <> 0) (λ x, x^2-1/x^2).
