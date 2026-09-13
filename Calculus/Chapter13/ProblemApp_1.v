From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_app_1 : ∀ f g a b,
  a < b -> continuous_on f [a, b] -> continuous_on g [a, b] ->
  ∀ ε, ε > 0 -> ∃ δ, δ > 0 /\
  ∀ (P : partition a b) (x u : list R),
    mesh_lt a b P δ -> is_tagging a b P x -> is_tagging a b P u ->
    let t := points a b P in
    |(∑ 0 (List.length t - 2) (λ i, f (x.[i]) * g (u.[i]) * (t.[i+1] - t.[i]))) -
      ∫ a b (f ⋅ g)| < ε.
Abort.
