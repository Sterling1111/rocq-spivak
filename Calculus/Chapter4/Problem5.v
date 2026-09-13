From Calculus.Chapter4 Require Import Prelude.

(* Draw each of these point sets. In 5(ii), assume a > 0 and b > 0.
   In 4, (iii) and (iv) are identical in the PDF and are both retained. *)

Definition problem_4_5_i : Ensemble point :=
  locus (λ x y, x = y^2).

Definition problem_4_5_ii (a b : ℝ) : Ensemble point :=
  locus (λ x y, y^2/a^2-x^2/b^2 = 1).

Definition problem_4_5_iii : Ensemble point :=
  locus (λ x y, x = |y|).

Definition problem_4_5_iv : Ensemble point :=
  locus (λ x y, x = sin y).
