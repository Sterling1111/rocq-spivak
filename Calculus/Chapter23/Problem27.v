From Calculus.Chapter23 Require Import Prelude.

(* Problem 27: Infinite products *)

Definition prod_f (i n : nat) (f : nat -> R) : R.
Abort. (* Assuming a product notation or definition is provided *)

Definition infinite_product_converges (b : sequence) : Prop :=
  exists L, L <> 0 /\ ⟦ lim ⟧ (fun n => prod_f 1 n b) = L.

Lemma problem_23_27_a : forall a,
  (forall n, a n > 0) ->
  (infinite_product_converges (fun n => 1 + a n) <-> exists S, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a n) = S).
Abort.

Lemma problem_23_27_b : forall a,
  (forall n, a n > 0) ->
  (infinite_product_converges (fun n => 1 + a n) <-> exists S, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else log (1 + a n)) = S).
Abort.
