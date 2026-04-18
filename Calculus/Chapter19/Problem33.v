From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_33 : forall f n,
  (forall k, (k <= n)%nat -> continuous (D k f)) ->
  exists P, ∫ 0 1 (D n f) = P.
Abort.
