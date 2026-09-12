From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_8_a : ∀ n x,
  P(4*n+2, 0, λ y, sin (y^2)) x =
    ∑ 0 n (λ k, (-1)^k / (fact (2*k+1)) * x^(4*k+2)).
Abort.

Lemma lemma_20_8_b : ∀ k : ℕ,
  ⟦ der ^ k 0 ⟧ (λ x, sin (x^2)) =
    (λ _, if Nat.eq_dec (k mod 4) 2
          then (-1)^(k/4) * (fact k) / (fact (k/2)) else 0).
Abort.

Lemma lemma_20_8_c : ∀ g m k,
  (0 < m)%nat -> (∀ j, nth_differentiable j g) ->
  ⟦ der ^ k 0 ⟧ (λ x, g (x^m)) =
    (λ _, if Nat.eq_dec (k mod m) 0
          then (fact k) / (fact (k/m)) * ⟦ Der ^ (k/m) 0 ⟧ g else 0).
Abort.
