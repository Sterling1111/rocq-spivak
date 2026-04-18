From Calculus.Chapter23 Require Import Prelude.

(* Problem 24: \lim n a_n = 0 for convergent sum of decreasing sequence *)

Lemma problem_23_24 : forall a,
  (forall n, a n > 0) ->
  decreasing a ->
  (exists S, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a n) = S) ->
  ⟦ lim ⟧ (fun n => INR n * a n) = 0.
Abort.
