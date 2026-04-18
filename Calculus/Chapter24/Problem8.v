From Calculus.Chapter24 Require Import Prelude.

Lemma lemma_24_8 :
  ~ (forall (fn : nat -> R -> R) (Mn : nat -> R) A f,
      (forall n x, x ∈ A -> 0 <= fn n x <= Mn n) ->
      (forall n (ε : R), ε > 0 -> exists x, x ∈ A /\ fn n x > Mn n - ε) ->
      uniform_limit (fun N x => ∑ 0 N (fun n => fn n x)) f A ->
      series_converges Mn).
Abort.
