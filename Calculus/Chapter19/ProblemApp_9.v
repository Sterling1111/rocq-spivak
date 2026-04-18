From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_App_9 : forall h A,
  h > 0 -> A > 0 ->
  ∫ 0 h (fun y => A * (y / h)^2) = A * h / 3.
Abort.
