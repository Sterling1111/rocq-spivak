From Calculus.Chapter23 Require Import Prelude.
Require Import Calculus.Chapter23.Problem_23_12. (* For cesaro_summable *)

(* Problem 13: Hardy's Tauberian Theorem *)

Lemma problem_23_13 : forall a l,
  (forall n, a n > 0) ->
  cesaro_summable a l ->
  bounded (fun n => INR n * a n) ->
  exists S, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a n) = S.
Admitted.
