From Calculus.Chapter14 Require Import Prelude.

(* Problem 17: Use the Fundamental Theorem of Calculus and Darboux's Theorem
   to give another proof of the Intermediate Value Theorem. *)

Lemma lemma_14_17 : forall f a b,
  a < b ->
  continuous_on f [a, b] ->
  forall y, Rmin (f a) (f b) <= y <= Rmax (f a) (f b) ->
  exists c, c ∈ [a, b] /\ f c = y.
Admitted.
