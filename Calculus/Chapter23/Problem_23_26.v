From Calculus.Chapter23 Require Import Prelude.

(* Problem 26: \sum a_n diverges => \sum a_n/(1+a_n) diverges *)

Lemma problem_23_26 : forall a,
  (forall n, a n >= 0) ->
  ~ (exists S, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a n) = S) ->
  ~ (exists S, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a n / (1 + a n)) = S).
Admitted.
