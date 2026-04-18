From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_19 : forall a f,
  series_converges a ->
  (forall x, 0 <= x <= 1 -> ∑ 0 ∞ (fun n => a n * x^n) = (f x)) ->
  uniform_limit (fun N x => ∑ 0 N (fun n => a n * x^n)) f (fun x => 0 <= x <= 1).
Abort.
