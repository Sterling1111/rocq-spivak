From Calculus.Chapter4 Require Import Prelude.

(* Draw each point set. *)

Definition problem_4_3_i : Ensemble point :=
  locus (λ x y, x > y).

Definition problem_4_3_ii (a b : ℝ) : Ensemble point :=
  locus (λ x y, x+a > y+b).

Definition problem_4_3_iii : Ensemble point :=
  locus (λ x y, y < x^2).

Definition problem_4_3_iv : Ensemble point :=
  locus (λ x y, y <= x^2).

Definition problem_4_3_v : Ensemble point :=
  locus (λ x y, |x-y| < 1).

Definition problem_4_3_vi : Ensemble point :=
  locus (λ x y, |x+y| < 1).

Definition problem_4_3_vii : Ensemble point :=
  locus (λ x y, is_integer (x+y)).

Definition problem_4_3_viii : Ensemble point :=
  locus (λ x y, x+y <> 0 /\ is_integer (1/(x+y))).

Definition problem_4_3_ix : Ensemble point :=
  locus (λ x y, (x-1)^2+(y-2)^2 < 1).

Definition problem_4_3_x : Ensemble point :=
  locus (λ x y, x^2 < y < x^4).
