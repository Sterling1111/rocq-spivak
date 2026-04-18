From Calculus.Chapter19 Require Import Prelude.

(* Problem 14: Where does C come from in e^x sin x integration? *)

Lemma lemma_19_14 : forall F c,
  (forall x, F x = exp x * (sin x - cos x) / 2 + c) ->
  ⟦ der ⟧ F = (fun x => exp x * sin x).
Abort.
