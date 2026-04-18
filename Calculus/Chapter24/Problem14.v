From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_14_even : forall a R_val,
  R_val > 0 ->
  (forall x, Rabs x < R_val -> series_converges (fun n => a n * x^n)) ->
  (forall x S, Rabs x < R_val -> (∑ 0 ∞ (fun n => a n * x^n) = S) -> (∑ 0 ∞ (fun n => a n * (-x)^n) = S)) ->
  forall n, Nat.Odd n -> a n = 0.
Abort.

Lemma lemma_24_14_odd : forall a R_val,
  R_val > 0 ->
  (forall x, Rabs x < R_val -> series_converges (fun n => a n * x^n)) ->
  (forall x S, Rabs x < R_val -> ∑ 0 ∞ (fun n => a n * x^n) = S -> ∑ 0 ∞ (fun n => a n * (-x)^n) = (- S)) ->
  forall n, Nat.Even n -> a n = 0.
Abort.
