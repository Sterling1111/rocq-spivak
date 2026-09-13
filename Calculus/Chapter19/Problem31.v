From Calculus.Chapter19 Require Import Prelude.

Definition polar_length_19 (f : R -> R) (a b L : R) :=
  has_length_19 (λ θ, f θ*cos θ) (λ θ, f θ*sin θ) a b L.
Lemma lemma_19_31_i : ∀ a, 0 < a ->
  polar_length_19 (λ θ, a*cos θ) (-π/2) (π/2) (π*a).
Abort.

Lemma lemma_19_31_ii : ∀ a, 0 < a ->
  polar_length_19 (λ θ, a*(1-cos θ)) 0 (2*π) (8*a).
Abort.

Lemma lemma_19_31_iii : ∀ a, 0 < a ->
  polar_length_19 (λ θ, a*sin (θ/2)^2) 0 (2*π) (4*a).
Abort.

Lemma lemma_19_31_iv : polar_length_19 (λ θ, θ) 0 (2*π)
  (π*√(1+4*π^2) + log (2*π+√(1+4*π^2))/2).
Abort.

Lemma lemma_19_31_v : polar_length_19 (λ θ, 3/cos θ) 0 (π/3) (3*√3).
Abort.
