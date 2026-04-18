From Calculus.Chapter23 Require Import Prelude.

(* Problem 22: Cauchy Condensation Theorem *)

Lemma problem_23_22 : forall a,
  decreasing a ->
  ⟦ lim ⟧ a = 0 ->
  (exists S1, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a n) = S1) <->
  (exists S2, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else 2^n * a (2^n)%nat) = S2).
Abort.
