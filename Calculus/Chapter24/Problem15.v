From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_15_a : forall x,
  series_converges (fun n => if Nat.eq_dec n 0 then 0 else - x^n / INR n) <->
  -1 <= x < 1.
Abort.

Lemma lemma_24_15_b : forall x,
  series_converges (fun n => if Nat.eq_dec n 0 then 0 else if Nat.even n then 0 else 2 * x^n / INR n) <->
  -1 < x < 1.
Abort.
