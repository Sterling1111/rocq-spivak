From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_18 : forall (a : nat -> R) x0,
  a 0%nat = 1 ->
  x0 <> 0 -> series_converges (fun n => a n * x0^n) ->
  exists (b : nat -> R),
    b 0%nat = 1 /\ (forall n, (n > 0)%nat -> b n = - ∑ 0 (n - 1) (fun k => b k * a (n - k)%nat)) /\
    exists x1, x1 <> 0 /\ series_converges (fun n => b n * x1^n).
Admitted.
