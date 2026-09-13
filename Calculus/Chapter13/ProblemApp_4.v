From Calculus.Chapter13 Require Import Prelude.

From Calculus.Chapter13 Require Import ProblemApp_3.

Lemma lemma_13_app_4 : ∀ f f' θ0 θ1,
  θ0 < θ1 -> derivative_on f f' [θ0, θ1] -> continuous_on f' [θ0, θ1] ->
  is_parametric_length θ0 θ1 (λ θ, f θ * cos θ) (λ θ, f θ * sin θ)
    (∫ θ0 θ1 (λ θ, √(f θ ^ 2 + f' θ ^ 2))).
Abort.
