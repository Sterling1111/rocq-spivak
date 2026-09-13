From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_29_a : ∀ fn f a b,
  (∀ n, continuous_on (fn n) (λ x, a <= x <= b)) ->
  uniform_limit fn f (λ x, a <= x <= b) ->
  ∀ (xn : nat -> R) x,
  (∀ n, a <= xn n <= b) -> a <= x <= b ->
  ⟦ lim ⟧ xn = x -> ⟦ lim ⟧ (λ n, fn n (xn n)) = f x.
Abort.

Lemma lemma_24_29_c : ∀ fn f a b,
  continuous_on f (λ x, a <= x <= b) ->
  (∀ (xn : nat -> R) x,
    (∀ n, a <= xn n <= b) -> a <= x <= b ->
    ⟦ lim ⟧ xn = x -> ⟦ lim ⟧ (λ n, fn n (xn n)) = f x) ->
  uniform_limit fn f (λ x, a <= x <= b).
Abort.
