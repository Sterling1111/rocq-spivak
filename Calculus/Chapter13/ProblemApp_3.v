From Calculus.Chapter13 Require Import Prelude.

Definition parametric_polygonal_length {a b : R}
  (u v : R -> R) (P : partition a b) : R :=
  let t := points a b P in
  ∑ 0 (List.length t - 2) (λ i,
    √((u (t.[i+1]) - u (t.[i]))^2 + (v (t.[i+1]) - v (t.[i]))^2)).

Definition is_parametric_length (a b : R) (u v : R -> R) (L : R) : Prop :=
  is_lub (λ y, ∃ P : partition a b, y = parametric_polygonal_length u v P) L.

Lemma lemma_13_app_3 : ∀ u v u' v' a b,
  a < b -> derivative_on u u' [a, b] -> derivative_on v v' [a, b] ->
  continuous_on u' [a, b] -> continuous_on v' [a, b] ->
  is_parametric_length a b u v (∫ a b (λ t, √(u' t ^ 2 + v' t ^ 2))).
Abort.
