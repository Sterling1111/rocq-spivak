From Calculus.Chapter4 Require Import Prelude.

(* {x} is distance to the nearest integer, not fractional part. Sketch each. *)
Definition nearest_integer_distance (x : ℝ) : ℝ :=
  Rmin (x-(Zfloor x)%Z) ((Zfloor x)%Z+1-x).

Definition problem_4_18_i := graph (λ x, nearest_integer_distance x).

Definition problem_4_18_ii := graph (λ x, nearest_integer_distance (2*x)).

Definition problem_4_18_iii := graph (λ x, nearest_integer_distance x + (1/2)*nearest_integer_distance (2*x)).

Definition problem_4_18_iv := graph (λ x, nearest_integer_distance (4*x)).

Definition problem_4_18_v := graph (λ x, nearest_integer_distance x + (1/2)*nearest_integer_distance (2*x) + (1/4)*nearest_integer_distance (4*x)).
