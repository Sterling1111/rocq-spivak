From Calculus.Chapter23 Require Import Prelude.
Require Import Lib.Partition.
(* Problem 18: Unbounded length (variation) of x sin(1/x) *)

Definition length_of_partition (f : R -> R) (P : list R) : R :=
  ∑ 1 (length P - 1) (fun i => √ ((nth i P 0 - nth (i-1) P 0)^2 + (f (nth i P 0) - f (nth (i-1) P 0))^2)).

Lemma problem_23_18 :
  let f := fun x => if Req_dec_T x 0 then 0 else x * sin (1 / x) in
  ~ (exists M : R, forall l : R, (exists P : partition 0 1, l = length_of_partition f (points 0 1 P)) -> l <= M).
Admitted.
