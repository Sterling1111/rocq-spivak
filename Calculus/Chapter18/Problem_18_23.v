From Calculus.Chapter18 Require Import Prelude.

(* Problem 23: Prove that if f(x) = \int_0^x f(t) dt, then f = 0. *)
Lemma problem_18_23 : forall f, (forall x, f x = ∫ 0 x f) -> f = fun _ => 0. Admitted.
