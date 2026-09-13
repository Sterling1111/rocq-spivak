From Calculus.Chapter4 Require Import Prelude.

Lemma lemma_4_21_a :
  ∀ x : ℝ,
    distance_to_set (pair x (x^2)) (graph (λ _, -1/4))
      (distance (pair x (x^2)) (pair 0 (1/4))).
Abort.

Lemma lemma_4_21_b :
  ∀ alpha beta gamma : ℝ, beta <> gamma ->
    ∃ a b c : ℝ, a <> 0 /\ ∀ x y : ℝ,
      (distance_to_set (pair x y) (graph (λ _, gamma))
        (distance (pair x y) (pair alpha beta)) <-> y=a*x^2+b*x+c).
Abort.

Lemma lemma_4_21_b_degenerate :
  ∀ alpha beta x y : ℝ,
    (distance_to_set (pair x y) (graph (λ _, beta))
      (distance (pair x y) (pair alpha beta)) <-> x=alpha).
Abort.
