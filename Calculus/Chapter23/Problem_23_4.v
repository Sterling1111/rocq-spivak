From Calculus.Chapter23 Require Import Prelude.

(* Problem 4: Decide whether or not \sum_{n=1}^{\infty} 1/n^{1+1/n} converges. *)

Lemma problem_23_4 :
  ~ (exists S, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else 1 / (INR n)^(1 + 1 / INR n)) = S).
Admitted.
