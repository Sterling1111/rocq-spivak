From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_28 : ∀ f f' g θ0 θ1,
  θ0 < θ1 -> derivative_on f f' [θ0, θ1] -> continuous_on f' [θ0, θ1] ->
  let u := λ θ, f θ * cos θ in
  let v := λ θ, f θ * sin θ in
  decreasing_on u [θ0, θ1] -> continuous_on g [u θ1, u θ0] ->
  (∀ θ, θ0 <= θ <= θ1 -> g (u θ) = v θ) ->
  ∫ θ0 θ1 (λ θ, f θ^2)/2 =
    u θ1*v θ1/2 + ∫ (u θ1) (u θ0) g - u θ0*v θ0/2.
Abort.
