From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_11 : forall n g a,
  (forall k, (k <= n)%nat -> ⟦ Der ^ k a ⟧ g = 0) ->
  equal_up_to_order n (fun x => exp (g x)) (fun x => 1) a.
Abort.
