From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_42_a_i : ∀ n,
  ∫ 0 1 (λ x, (1-x^2)^n) = product_19 n (λ k, (2*k)/(2*k+1)).
Abort.
Lemma lemma_19_42_a_ii : ∀ n : nat, (0 < n)%nat ->
  improper_integral_pinf 0 (λ x, 1/(1+x^2)^n)
    (π/2 * product_19 (n-1) (λ k, (2*k-1)/(2*k))).
Abort.
Lemma lemma_19_42_b_i : ∀ x, 0 <= x <= 1 -> 1-x^2 <= exp (-x^2).
Abort.
Lemma lemma_19_42_b_ii : ∀ x, 0 <= x -> exp (-x^2) <= 1/(1+x^2).
Abort.
Lemma lemma_19_42_c : ∃ I, improper_integral_pinf 0 (λ y, exp (-y^2)) I /\
  ∀ n : nat, (0 < n)%nat ->
  √n * product_19 n (λ k, (2*k)/(2*k+1)) <= ∫ 0 (√n) (λ y, exp (-y^2)) /\
  ∫ 0 (√n) (λ y, exp (-y^2)) <= I /\
  I <= π/2 * √n * product_19 (n-1) (λ k, (2*k-1)/(2*k)).
Abort.
Lemma lemma_19_42_d : improper_integral_pinf 0 (λ y, exp (-y^2)) (√π/2).
Abort.
