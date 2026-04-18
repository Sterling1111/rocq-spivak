From Calculus.Chapter23 Require Import Prelude.
Require Import Calculus.Chapter23.Problem27. (* For infinite product definitions *)

(* Problem 28: Explicit computation of products *)

Lemma problem_23_28_a :
  exists L, L <> 0 /\ ⟦ lim ⟧ (fun N => prod_f 2 N (fun n => 1 - 1 / INR n^2)) = L /\ L = 1/2.
Abort.

Lemma problem_23_28_b : forall x,
  |x| < 1 ->
  exists L, L <> 0 /\ ⟦ lim ⟧ (fun N => prod_f 1 N (fun n => 1 + x^(2^n)%nat)) = L /\ L = 1 / (1 - x).
Abort.
