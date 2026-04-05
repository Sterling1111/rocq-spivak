From Calculus.Chapter21 Require Import Prelude.

(* Problem 1 *)

(* (a) Prove that if α > 0 is algebraic, then √α is algebraic. *)
Lemma lemma_21_1_a : forall α,
  α > 0 -> algebraic α -> algebraic (√α).
Admitted.

(* (b) Prove that if α is algebraic and r is rational, then α+r and αr are algebraic. *)
Lemma lemma_21_1_b : forall α r,
  algebraic α -> (exists q : Q, r = Q2R q) ->
  algebraic (α + r) /\ algebraic (α * r).
Admitted.
