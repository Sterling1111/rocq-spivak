From Calculus.Chapter4 Require Import Prelude.

Lemma lemma_4_8_a :
  ∀ m n b c : ℝ, m*n = -1 -> perpendicular (graph (λ x, m*x+b)) (graph (λ x, n*x+c)).
Abort.

Lemma lemma_4_8_a_triangle :
  ∀ m n : ℝ, m*n = -1 -> distance (pair (1) (m)) (pair (1) (n))^2 = distance (pair (0) (0)) (pair (1) (m))^2 + distance (pair (0) (0)) (pair (1) (n))^2.
Abort.

Lemma lemma_4_8_b :
  ∀ A B C A' B' C' : ℝ, (A <> 0 \/ B <> 0) -> (A' <> 0 \/ B' <> 0) -> (perpendicular (line_equation A B C) (line_equation A' B' C') <-> A*A'+B*B'=0).
Abort.
