From Calculus.Chapter19 Require Import Prelude.

Definition sine_integral_19 (n : nat) := ∫ 0 (π/2) (λ x, sin x^n).
Lemma lemma_19_41_a : ∀ n : nat, (2 <= n)%nat ->
  sine_integral_19 n = (n-1)/n * sine_integral_19 (n-2).
Abort.

Lemma lemma_19_41_b_odd : ∀ n,
  sine_integral_19 (2*n+1) = product_19 n (λ k, (2*k)/(2*k+1)).
Abort.

Lemma lemma_19_41_b_even : ∀ n,
  sine_integral_19 (2*n) = π/2 * product_19 n (λ k, (2*k-1)/(2*k)).
Abort.

Lemma lemma_19_41_b : ∀ n,
  π/2 = product_19 n (λ k, (2*k)^2/((2*k-1)*(2*k+1))) *
    (sine_integral_19 (2*n) / sine_integral_19 (2*n+1)).
Abort.

Lemma lemma_19_41_c_bounds : ∀ n : nat, (0 < n)%nat ->
  1 <= sine_integral_19 (2*n) / sine_integral_19 (2*n+1) <= 1 + 1/(2*n).
Abort.

Lemma lemma_19_41_c : sequence_limit_19
  (λ n, product_19 n (λ k, (2*k)^2/((2*k-1)*(2*k+1)))) (π/2).
Abort.

Lemma lemma_19_41_d : sequence_limit_19
  (λ n, product_19 n (λ k, (2*k)/(2*k-1)) / √n) (√π).
Abort.
