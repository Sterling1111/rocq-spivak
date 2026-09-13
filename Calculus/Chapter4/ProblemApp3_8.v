From Calculus.Chapter4 Require Import Prelude.

(* (a) Sketch this cardioid. *)
Definition problem_4_app3_8_a := polar_graph (λ theta, 1-sin theta).

Lemma lemma_4_app3_8_b :
  polar_graph (λ theta, 1-sin theta) =
    polar_graph (λ theta, -1-sin theta).
Abort.

Lemma lemma_4_app3_8_c_radical :
  ∀ x y : ℝ,
    (pair x y ∈ polar_graph (λ theta, 1-sin theta) <->
     x^2+y^2=√(x^2+y^2)-y).
Abort.

Lemma lemma_4_app3_8_c_polynomial :
  ∀ x y : ℝ,
    (pair x y ∈ polar_graph (λ theta, 1-sin theta) <->
     (x^2+y^2+y)^2=x^2+y^2).
Abort.
