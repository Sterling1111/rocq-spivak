From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_27_i : ∀ a, 0 < a ->
  ∫ 0 π (λ θ, (a*sin θ)^2)/2 = π*a^2/4.
Abort.

Lemma lemma_19_27_ii : ∫ 0 (2*π) (λ θ, (2+cos θ)^2)/2 = 9*π/2.
Abort.

Lemma lemma_19_27_iii : ∀ a, 0 < a ->
  2 * (∫ (-π/4) (π/4) (λ θ, 2*a^2*cos (2*θ))/2) = 2*a^2.
Proof.
  intros a H1.
Abort.

Lemma lemma_19_27_iv : ∀ a, 0 < a ->
  ∫ 0 (2*π) (λ θ, (a*cos (2*θ))^2)/2 = π*a^2/2.
Abort.
