From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_26 : forall phi,
  (forall x, phi x >= 0) ->
  (forall x, Rabs x >= 1 -> phi x = 0) ->
  ∫ (-1) 1 phi = 1 ->
  ∫ (-1) 1 (fun x => phi (-x)) = 1.
Admitted.
