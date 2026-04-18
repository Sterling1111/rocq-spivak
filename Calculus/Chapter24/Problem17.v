From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_17 : forall a b c x,
  (forall n, c n = ∑ 0 n (fun k => a k * b (n - k))) ->
  series_converges (fun n => a n * x^n) ->
  series_converges (fun n => b n * x^n) ->
  series_converges (fun n => c n * x^n) /\
  forall A B, ∑ 0 ∞ (fun n => a n * x^n) = A -> ∑ 0 ∞ (fun n => b n * x^n) = B -> ∑ 0 ∞ (fun n => c n * x^n) = (A * B).
Abort.
