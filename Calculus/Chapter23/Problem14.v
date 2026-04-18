From Calculus.Chapter23 Require Import Prelude.

(* Problem 14: Alternative proof of Theorem 8 outline *)

(* (a) Subsequence of absolutely convergent series converges absolutely. *)
Lemma problem_23_14_a : forall a (sub : sequence),
  series_converges_absolutely a ->
  (forall n, exists m, sub n = a m) /\ (forall n m : nat, (n < m)%nat -> exists (k j : nat), (k < j)%nat /\ sub n = a k /\ sub m = a j) -> (* sub is a subsequence *)
  series_converges_absolutely sub.
Abort.

(* (b) False if not absolutely convergent. *)
Lemma problem_23_14_b :
  ~ (forall a (sub : sequence),
       (exists S, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a n) = S) ->
       (forall n, exists m, sub n = a m) /\ (forall n m : nat, (n < m)%nat -> exists (k j : nat), (k < j)%nat /\ sub n = a k /\ sub m = a j) ->
       (exists S, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else sub n) = S)).
Abort.

(* (c) Sum equals evens plus odds. *)
Lemma problem_23_14_c : forall a S_odd S_even S_total,
  series_converges_absolutely a ->
  (∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a n) = S_total) ->
  (∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a (2 * n - 1)%nat) = S_odd) ->
  (∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a (2 * n)%nat) = S_even) ->
  S_total = S_odd + S_even.
Abort.
