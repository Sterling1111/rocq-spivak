From Calculus.Chapter14 Require Import Prelude.

(* Problem 22: Suppose f is differentiable with f(0) = 0 and 0 < f' ≤ 1.
   Prove that for all x ≥ 0, ∫ 0 x f^3 ≤ (∫ 0 x f)^2. *)

Lemma lemma_14_22 : forall f f',
  ⟦ der ⟧ f = f' ->
  f 0 = 0 ->
  (forall x, 0 < f' x <= 1) ->
  forall x, x >= 0 ->
  ∫ 0 x (fun t => (f t)^3) <= (∫ 0 x f)^2.
Abort.
