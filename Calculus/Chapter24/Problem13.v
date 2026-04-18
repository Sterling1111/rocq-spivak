From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_13_a : forall a R,
  R > 0 ->
  (forall x, Rabs x < R -> series_converges (fun n => a n * x^n) /\ ∑ 0 ∞ (fun n => a n * x^n) = 0) ->
  forall n, a n = 0.
Abort.

Lemma lemma_24_13_b : forall a (x : nat -> R),
  (forall n, x n <> 0) ->
  ⟦ lim ⟧ x = 0 ->
  (forall n, series_converges (fun k => a k * (x n)^k) /\ ∑ 0 ∞ (fun k => a k * (x n)^k) = 0) ->
  forall n, a n = 0.
Abort.

Lemma lemma_24_13_c : forall a b (x : nat -> R),
  (forall n, x n <> 0) ->
  ⟦ lim ⟧ x = 0 ->
  (forall n, series_converges (fun k => a k * (x n)^k) /\ series_converges (fun k => b k * (x n)^k) /\
             exists L, ∑ 0 ∞ (fun k => a k * (x n)^k) = L /\ ∑ 0 ∞ (fun k => b k * (x n)^k) = L) ->
  forall n, a n = b n.
Abort.
