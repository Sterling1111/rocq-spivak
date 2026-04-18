From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_23_a : forall f c,
  c < 1 ->
  (forall x y, Rabs (f x - f y) <= c * Rabs (x - y)) ->
  continuous f.
Abort.

Lemma lemma_22_23_b : forall f c,
  c < 1 ->
  (forall x y, Rabs (f x - f y) <= c * Rabs (x - y)) ->
  forall x y, f x = x -> f y = y -> x = y.
Abort.

Lemma lemma_22_23_c : forall f c x,
  0 <= c < 1 ->
  (forall x y, Rabs (f x - f y) <= c * Rabs (x - y)) ->
  exists b L, b 0%nat = x /\ (forall n, b (S n) = f (b n)) /\ ⟦ lim ⟧ b = L /\ f L = L.
Abort.
