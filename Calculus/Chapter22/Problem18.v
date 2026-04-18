From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_18 : forall a L,
  (forall n, a n >= 0) ->
  ⟦ lim ⟧ (fun n => a (n + 1)%nat / a n) = L ->
  ⟦ lim ⟧ (fun n => exp ((1 / INR n) * log (a n))) = L.
Abort.
