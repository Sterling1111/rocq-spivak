From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_12_a : ∀ x, cos (x/2) <> 0 ->
  sin x = 2 * tan (x/2) / (1 + tan (x/2)^2).
Abort.

Lemma lemma_19_12_b : ∀ x, cos (x/2) <> 0 ->
  cos x = (1 - tan (x/2)^2) / (1 + tan (x/2)^2).
Abort.

Lemma lemma_19_12_i : ∀ c,
  ∫ (λ x, 1 / (1 + sin x)) (-π/2, π/2) =
    (λ x, -2 / (1 + tan (x/2)) + c).
Proof.
  auto_int.
Abort.

Lemma lemma_19_12_ii : ∀ c,
  ∫ (λ x, 1 / (1 - sin x^2)) (-π/2, π/2) = (λ x, tan x + c).
Abort.

Lemma lemma_19_12_iii : ∀ a b r θ c, 0 < r ->
  a = r * cos θ -> b = r * sin θ ->
  ∫ (λ x, 1 / (a * sin x + b * cos x)) (-θ, π-θ) =
    (λ x, log (tan ((x+θ)/2)) / r + c).
Abort.

Lemma lemma_19_12_iv : ∀ c,
  ∫ (λ x, sin x^2) = (λ x, x/2 - sin (2*x)/4 + c).
Abort.

Lemma lemma_19_12_v : ∀ c,
  ∫ (λ x, 1 / (3 + 5*sin x)) (0, π) =
    (λ x, log ((3*tan (x/2)+1)/(tan (x/2)+3))/4 + c).
Abort.
