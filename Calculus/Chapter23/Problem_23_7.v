From Calculus.Chapter23 Require Import Prelude.

(* Problem 7 *)

(* (a) Prove that if 0 <= a_n <= 9 (integer), then \sum a_n 10^{-n} exists and is in [0, 1]. *)
Lemma problem_23_7_a : forall a,
  (forall n, (n > 0)%nat -> 0 <= a n /\ a n <= 9) ->
  (forall n, (n > 0)%nat -> exists (k : nat), a n = INR k) ->
  exists S, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a n / 10^n) = S /\ 0 <= S /\ S <= 1.
Admitted.

(* (b) Prove that for any x in [0, 1], there is such a sequence. *)
Lemma problem_23_7_b : forall x,
  0 <= x <= 1 ->
  exists a S,
    (forall n, (n > 0)%nat -> 0 <= a n /\ a n <= 9) /\
    (forall n, (n > 0)%nat -> exists (k : nat), a n = INR k) /\
    ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a n / 10^n) = S /\ S = x.
Admitted.

Definition eventually_repeating (a : sequence) : Prop :=
  exists N p, (p > 0)%nat /\ forall n, (n >= N)%nat -> a (n + p)%nat = a n.

(* (c) Show that if sequence is eventually repeating, the sum is a rational number. *)
Lemma problem_23_7_c : forall a x,
  (forall n, (n > 0)%nat -> 0 <= a n /\ a n <= 9) ->
  (forall n, (n > 0)%nat -> exists (k : nat), a n = INR k) ->
  eventually_repeating a ->
  ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a n / 10^n) = x ->
  rational x.
Admitted.

(* (d) Show that if the sum is rational, the sequence is eventually repeating. *)
Lemma problem_23_7_d : forall a x,
  (forall n, (n > 0)%nat -> 0 <= a n /\ a n <= 9) ->
  (forall n, (n > 0)%nat -> exists (k : nat), a n = INR k) ->
  ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a n / 10^n) = x ->
  rational x ->
  eventually_repeating a.
Admitted.
