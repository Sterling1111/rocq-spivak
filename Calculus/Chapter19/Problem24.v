From Calculus.Chapter19 Require Import Prelude.

(* Problem 24: Prove that \int_a^b f(x) dx = \int_a^b f(a+b-x) dx. *)
Lemma problem_19_24 : forall f a b,
  ∫ a b f = ∫ a b (fun x => f (a + b - x)). Abort.
