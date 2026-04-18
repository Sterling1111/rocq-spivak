From Calculus.Chapter24 Require Import Prelude.

(* (a) Missing statements in text. *)
Lemma lemma_24_21_a : True.
Abort.

Lemma lemma_24_21_b : forall a b c,
  (forall n, c n = ∑ 0 n (fun k => a k * b (n - k))) ->
  series_converges a -> series_converges b -> series_converges c ->
  forall A B, ∑ 0 ∞ a = A -> ∑ 0 ∞ b = B -> ∑ 0 ∞ c = (A * B).
Abort.
