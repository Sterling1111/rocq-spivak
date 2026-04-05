From Calculus.Chapter23 Require Import Prelude.

(* Problem 20: Binomial series *)

Fixpoint generalized_choose (α : R) (k : nat) : R :=
  match k with
  | O => 1
  | S k' => (α - INR k') / INR k * generalized_choose α k'
  end.

Lemma problem_23_20 : forall α x,
  |x| < 1 ->
  (exists S, ∑ 0 ∞ (fun k => generalized_choose α k * x^k) = S) /\
  (exists S, ∑ 0 ∞ (fun k => generalized_choose α k * x^k) = S /\ S = Rpower (1 + x) α). (* assuming x^y for real base is Rpower *)
Admitted.
