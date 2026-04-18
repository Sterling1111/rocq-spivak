From Calculus.Chapter23 Require Import Prelude.
Require Import Reals.Rpower.

(* Problem 23 *)

(* (a) If \sum a_n^2 and \sum b_n^2 converge, then \sum a_n b_n converges. *)
Lemma problem_23_23_a : forall a b,
  (exists S1, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else (a n)^2) = S1) ->
  (exists S2, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else (b n)^2) = S2) ->
  exists S3, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a n * b n) = S3.
Abort.

(* (b) If \sum a_n^2 converges, \sum a_n/n^\alpha converges for \alpha > 1/2. *)
Lemma problem_23_23_b : forall a α,
  (exists S1, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else (a n)^2) = S1) ->
  α > 1 / 2 ->
  exists S2, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a n / Rpower (INR n) α) = S2.
Abort.
