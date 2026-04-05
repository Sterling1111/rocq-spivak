From Calculus.Chapter23 Require Import Prelude.

(* Problem 12: Cesaro Summability *)

Definition cesaro_summable (a : sequence) (l : R) : Prop :=
  ⟦ lim ⟧ (fun n => (∑ 1 n (fun k => ∑ 1 k a)) / INR n) = l.

Lemma problem_23_12 :
  exists a l, cesaro_summable a l /\ ~ (exists S, ∑ 0 ∞ (fun n => if (n =? 0)%nat then 0 else a n) = S).
Admitted.
