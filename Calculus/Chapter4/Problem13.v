From Calculus.Chapter4 Require Import Prelude.

(* (a) Sketch and compare these two graphs. *)
Definition problem_4_13_a_abs := graph (λ x, |x|).
Definition problem_4_13_a_square := graph (λ x, x^2).

(* (b) Sketch and compare these graphs; identify the qualitative difference
   suggested by (a), particularly at their zeros. *)
Definition problem_4_13_b_abs := graph (λ x, |sin x|).
Definition problem_4_13_b_square := graph (λ x, (sin x)^2).
