From Calculus.Chapter4 Require Import Prelude.

(* Appendix 3, p. 88. Geometric interpretation: the cosine rule. *)
Lemma lemma_4_app3_1 :
  ∀ r1 theta1 r2 theta2 : ℝ,
    distance (polar_point r1 theta1) (polar_point r2 theta2)^2 =
    r1^2+r2^2-2*r1*r2*cos (theta1-theta2).
Abort.
