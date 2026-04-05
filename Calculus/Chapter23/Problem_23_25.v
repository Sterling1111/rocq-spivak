From Calculus.Chapter23 Require Import Prelude.

(* Problem 25: Counterexample to bounded partial sums + \lim = 0 => convergence *)

Lemma problem_23_25 :
  ~ (forall a,
      bounded (fun n => ∑ 1 n a) ->
      ⟦ lim ⟧ a = 0 ->
      exists S, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a n) = S).
Admitted.
