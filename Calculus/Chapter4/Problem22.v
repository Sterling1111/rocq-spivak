From Calculus.Chapter4 Require Import Prelude.

Lemma lemma_4_22_a_square :
  ∀ c d m x : ℝ,
    distance (pair c d) (pair x (m*x))^2 =
    x^2*(m^2+1)+x*(-2*m*d-2*c)+d^2+c^2.
Abort.

Lemma lemma_4_22_a :
  ∀ c d m : ℝ,
    distance_to_set (pair c d) (graph (λ x, m*x)) (|c*m-d|/√(m^2+1)).
Abort.

Lemma lemma_4_22_b :
  ∀ c d m b : ℝ,
    distance_to_set (pair c d) (graph (λ x, m*x+b)) (|c*m-d+b|/√(m^2+1)).
Abort.
