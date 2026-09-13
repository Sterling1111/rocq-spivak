From Calculus.Chapter4 Require Import Prelude.

(* Draw each point set. Parts (iii) and (iv) are identical in the PDF. *)

Definition problem_4_4_i : Ensemble point :=
  locus (λ x y, |x|+|y| = 1).

Definition problem_4_4_ii : Ensemble point :=
  locus (λ x y, |x| - |y| = 1).

Definition problem_4_4_iii : Ensemble point :=
  locus (λ x y, |x-1| = |y-1|).

Definition problem_4_4_iv : Ensemble point :=
  locus (λ x y, |1-x| = |y-1|).

Definition problem_4_4_v : Ensemble point :=
  locus (λ x y, x^2+y^2 = 0).

Definition problem_4_4_vi : Ensemble point :=
  locus (λ x y, x*y = 0).

Definition problem_4_4_vii : Ensemble point :=
  locus (λ x y, x^2-2*x+y^2 = 4).

Definition problem_4_4_viii : Ensemble point :=
  locus (λ x y, x^2 = y^2).
