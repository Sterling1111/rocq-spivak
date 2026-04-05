From Calculus.Chapter14 Require Import Prelude.

(* Problem 8: Find F'(x) if F(x) = ∫ 0 x (x * f(t)) dt.
   The answer is not x * f(x); perform an obvious manipulation first. *)

Lemma lemma_14_8 : forall f x,
  continuous f ->
  ⟦ der x ⟧ (fun x => ∫ 0 x (fun t => x * f t)) =
    (fun x => ∫ 0 x f + x * f x).
Admitted.
