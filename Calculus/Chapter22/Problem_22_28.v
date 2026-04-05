From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_28_a : forall f I x a,
  interval I -> x \in I ->
  (forall q : Q, (Q2R q) \in I <-> f (Q2R q) = f (Q2R q)) -> (* f is defined on Q in I *)
  (forall e, e > 0 -> exists d, d > 0 /\ forall q1 q2 : Q, Q2R q1 \in I -> Q2R q2 \in I ->
     Rabs (Q2R q1 - Q2R q2) < d -> Rabs (f (Q2R q1) - f (Q2R q2)) < e) ->
  (forall n, a n \in I) ->
  (forall n, exists q : Q, a n = Q2R q) ->
  ⟦ lim ⟧ a = x ->
  convergent_sequence (fun n => f (a n)).
Admitted.

Lemma lemma_22_28_bc : exists P, P = True.
Admitted.
