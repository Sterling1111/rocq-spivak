From Calculus.Chapter13 Require Import Prelude.

Definition sector_sum {a b : R} (P : partition a b) (r : nat -> R) : R :=
  let t := points a b P in
  ∑ 0 (List.length t - 2) (λ i, r i ^ 2 * (t.[i+1] - t.[i]) / 2).

Definition is_polar_area (f : R -> R) (a b A : R) : Prop :=
  is_lub (λ s, ∃ (P : partition a b) (r : nat -> R),
    (∀ i, (i < List.length (points a b P) - 1)%nat ->
      0 <= r i /\ ∀ x,
      x ∈ [(points a b P).[i], (points a b P).[i+1]] -> r i <= f x) /\
    s = sector_sum P r) A /\
  is_glb (λ s, ∃ (P : partition a b) (r : nat -> R),
    (∀ i, (i < List.length (points a b P) - 1)%nat ->
      0 <= r i /\ ∀ x,
      x ∈ [(points a b P).[i], (points a b P).[i+1]] -> f x <= r i) /\
    s = sector_sum P r) A.

Lemma lemma_13_24 : ∀ f θ0 θ1,
  θ0 < θ1 -> θ1 - θ0 <= 2 * PI ->
  continuous_on f [θ0, θ1] -> nonnegative_on f [θ0, θ1] ->
  is_polar_area f θ0 θ1 ((1 / 2) * ∫ θ0 θ1 (λ θ, f θ ^ 2)).
Abort.
