From Calculus.Chapter22 Require Import Prelude.

Definition limit_point_of_set (x : R) (A : R -> Prop) :=
  forall ε, ε > 0 -> exists a, A a /\ Rabs (x - a) < ε /\ x <> a.

Lemma lemma_22_30_a : exists P, P = True.
Abort.

Lemma lemma_22_30_b : forall x A,
  limit_point_of_set x A <-> 
  (forall ε, ε > 0 -> exists a : sequence, (forall n, A (a n) /\ Rabs (x - a n) < ε) /\
  (forall n m, n <> m -> a n <> a m)).
Abort.

Lemma lemma_22_30_cde : exists P, P = True.
Abort.
