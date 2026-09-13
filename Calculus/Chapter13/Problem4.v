From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_4_a : ∀ a b (P : partition a b) r,
  0 < a ->
  let t := points a b P in
  let n := (List.length t - 1)%nat in
  (∀ i, (i < n)%nat -> t.[i+1] / t.[i] = r) ->
  ∀ i, (i <= n)%nat -> t.[i] = a * Rpower (b / a) (i / n).
Abort.

Lemma lemma_13_4_b : ∀ a b (p n : nat)
  (H1 : 0 < a) (H2 : a < b) (H3 : (0 < n)%nat)
  (bf : bounded_function_R a b),
  bounded_f a b bf = (λ x, x ^ p) ->
  let P := geometric_partition a b n H1 H2 H3 in
  let c := b / a in
  U(bf, P) = a^(p+1) * (1 - Rpower c (-1 / n)) *
    (∑ 1 n (λ i, Rpower c ((p+1)%nat / n) ^ i)) /\
  U(bf, P) = (a^(p+1) - b^(p+1)) * Rpower c ((p+1)%nat / n) *
    (1 - Rpower c (-1 / n)) / (1 - Rpower c ((p+1)%nat / n)) /\
  U(bf, P) = (b^(p+1) - a^(p+1)) * Rpower c (p / n) /
    (∑ 0 p (λ (i : ℕ), Rpower c (i / n))) /\
  L(bf, P) = (b^(p+1) - a^(p+1)) /
    (∑ 0 p (λ (i : ℕ), Rpower c (i / n))).
Abort.

Lemma lemma_13_4_c : ∀ a b (p : nat),
  0 <= a < b -> ∫ a b (λ x, x^p) = (b^(p+1) - a^(p+1)) / (p+1)%nat.
Abort.
