From Calculus.Chapter14 Require Import Prelude.

(* Problem 14: Use the Fundamental Theorem of Calculus and Problem 13-21
   to derive the result stated in Problem 12-21. *)

Lemma lemma_14_14 : forall f a b n,
  (n > 0)%nat ->
  a < b ->
  continuous_on f [a, b] ->
  (forall x, x ∈ [a, b] -> f x >= 0) ->
  ∫ a b (fun x => (f x) ^ n) = 0 ->
  forall x, x ∈ [a, b] -> f x = 0.
Admitted.
