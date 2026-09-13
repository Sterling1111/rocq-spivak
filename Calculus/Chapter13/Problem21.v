From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_21_a : ∀ a b f g
  (bf : bounded_function_R (g a) (g b)) (bg : bounded_function_R a b)
  (P : partition a b) (Q : partition (g a) (g b)),
  bounded_f (g a) (g b) bf = f -> bounded_f a b bg = g ->
  increasing_on f [g a, g b] -> inverse_on f g [g a, g b] [a, b] ->
  points (g a) (g b) Q = map g (points a b P) ->
  L(bg, P) + U(bf, Q) = b * g b - a * g a.
Abort.

Lemma lemma_13_21_b : ∀ f g a b,
  a < b -> increasing_on f [g a, g b] ->
  inverse_on f g [g a, g b] [a, b] ->
  ∫ a b g = b * g b - a * g a - ∫ (g a) (g b) f.
Abort.

Lemma lemma_13_21_c : ∀ (n : nat) a b (root : R -> R),
  (0 < n)%nat -> 0 <= a < b ->
  (∀ x, 0 <= x -> 0 <= root x /\ root x ^ n = x) ->
  ∫ a b root = n / (n+1)%nat * (b * root b - a * root a).
Abort.
