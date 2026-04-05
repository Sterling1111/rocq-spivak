From Calculus.Chapter23 Require Import Prelude.

(* Problem 15: |\sum a_n| <= \sum |a_n| *)

Lemma problem_23_15 : forall a S_abs S_total,
  series_converges_absolutely a ->
  (∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a n) = S_total) ->
  (∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else |a n|) = S_abs) ->
  |S_total| <= S_abs.
Admitted.
