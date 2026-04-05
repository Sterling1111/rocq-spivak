From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_21_a : forall f x,
  continuous_on f (cc 0 1) ->
  (forall y, Rcc 0 1 y -> Rcc 0 1 (f y)) ->
  increasing_on f (cc 0 1) ->
  Rcc 0 1 x ->
  exists b L, b 0%nat = x /\ (forall n, b (S n) = f (b n)) /\ ⟦ lim ⟧ b = L /\ f L = L.
Admitted.

Lemma lemma_22_21_b : forall f g,
  continuous_on f (cc 0 1) -> continuous_on g (cc 0 1) ->
  (forall y, Rcc 0 1 y -> Rcc 0 1 (f y)) ->
  (forall y, Rcc 0 1 y -> Rcc 0 1 (g y)) ->
  (forall y, Rcc 0 1 y -> f (g y) = g (f y)) ->
  increasing_on f (cc 0 1) ->
  exists L, f L = L /\ g L = L.
Admitted.
