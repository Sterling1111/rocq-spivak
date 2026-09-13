From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_App_11_a : ∀ r,
  r > 0 ->
  2 * π * ∫ (-r) r (λ x, √(r^2 - x^2) * √(1 + (-x / √(r^2 - x^2))^2)) = 4 * π * r^2.
Abort.

Lemma lemma_19_App_11_b : ∀ r a b, 0 < r -> -r <= a -> a <= b -> b <= r ->
  2*π * ∫ a b (λ x, √(r^2-x^2)*√(1+(-x/√(r^2-x^2))^2)) = 2*π*r*(b-a).
Abort.

Lemma lemma_19_App_11_c : ∀ (n : nat) (w u v c : nat -> R) r,
  0 < r -> (2 <= n)%nat ->
  (∀ i, (1 <= i <= n)%nat -> 0 < w i /\ u i^2+v i^2 = 1) ->
  (∑ 1 n w) = 2*r ->
  (∃ i j, (1 <= i <= n)%nat /\ (1 <= j <= n)%nat /\ u i*v j-u j*v i <> 0) ->
  ∃ x y, x^2+y^2 <= r^2 /\
    ∀ i, (1 <= i <= n)%nat -> w i/2 < Rabs (u i*x+v i*y-c i).
Abort.
