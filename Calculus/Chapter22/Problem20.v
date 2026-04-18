From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_20 : forall f x L,
  continuous f ->
  (exists b, b 0%nat = x /\ (forall n, b (S n) = f (b n)) /\ ⟦ lim ⟧ b = L) ->
  f L = L.
Abort.
