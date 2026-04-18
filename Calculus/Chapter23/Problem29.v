From Calculus.Chapter23 Require Import Prelude.

(* Problem 29: Egyptian fractions definition *)

Definition is_distinct_egyptian_fractions (x : R) : Prop :=
  exists S_idx : list nat,
    NoDup S_idx /\ (forall n, In n S_idx -> (n > 0)%nat) /\
    x = ∑ 0 (length S_idx - 1) (fun i => 1 / INR (nth i S_idx O)).

(* (a) If 1/(n+1) < x < 1/n, the numerator in the exact sum string must decrease implicitly. *)
Lemma problem_23_29_a : forall x n,
  rational x -> x > 0 ->
  1 / (INR n + 1) < x -> x < 1 / INR n ->
  is_distinct_egyptian_fractions x.
Abort.

(* (b) Prove the result for all x by using the divergence of \sum 1/n. *)
Lemma problem_23_29_b : forall x,
  rational x -> x > 0 ->
  is_distinct_egyptian_fractions x.
Abort.
