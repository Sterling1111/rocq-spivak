From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_21_a : ∀ (n : nat) c, (2 <= n)%nat ->
  ∫ (λ x, sin x^n) =
    (λ x, -sin x^(n-1)*cos x/n + (n-1)/n * ∫ 0 x (λ t, sin t^(n-2)) + c).
Abort.

Lemma lemma_19_21_b : ∀ (n : nat) c, (2 <= n)%nat ->
  ∫ (λ x, cos x^n) =
    (λ x, cos x^(n-1)*sin x/n + (n-1)/n * ∫ 0 x (λ t, cos t^(n-2)) + c).
Abort.

Lemma lemma_19_21_c : ∀ (n : nat) c, (2 <= n)%nat ->
  ∫ (λ x, 1/(1+x^2)^n) =
    (λ x, x/(2*(n-1)*(1+x^2)^(n-1)) +
      (2*n-3)/(2*(n-1)) * ∫ 0 x (λ t, 1/(1+t^2)^(n-1)) + c).
Abort.
