From Calculus.Chapter23 Require Import Prelude.

(* Problem 10: Cauchy product divergence *)

Definition cauchy_product (a b : sequence) (n : nat) : R :=
  ∑ 1 n (fun k => a k * b (n + 1 - k)%nat).

Lemma problem_23_10 :
  let a := fun n => (-1)^n / √ (INR n) in
  let c := cauchy_product a a in
  (forall n, (n > 0)%nat -> |c n| >= 1) /\
  ~ exists S, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else c n) = S.
Abort.
