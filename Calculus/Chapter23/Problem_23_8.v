From Calculus.Chapter23 Require Import Prelude.

(* Problem 8: Leibniz's Theorem Error Estimate *)

Lemma problem_23_8 : forall a S N,
  (forall n, a n >= 0) ->
  decreasing a ->
  ⟦ lim ⟧ a = 0 ->
  (∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else (-1)^(n+1) * a n) = S) ->
  |S - ∑ 1 N (fun n => (-1)^(n+1) * a n)| <= a (S N).
Admitted.
