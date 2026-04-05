From Calculus.Chapter14 Require Import Prelude.

(* Problem 13: Find ∫ 0 b x^(1/n) dx by guessing an antiderivative and using the
   Second Fundamental Theorem of Calculus. *)

Lemma lemma_14_13 : forall (n : nat) b,
  (n > 0)%nat ->
  b > 0 ->
  ∫ 0 b (fun x => Rpower x (1 / INR n)) = Rpower b (1 / INR n + 1) / (1 / INR n + 1).
Admitted.
