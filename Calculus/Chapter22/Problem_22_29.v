From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_29_a : forall a x y : Q,
  a > 0 -> (Q2R x < Q2R y) ->
  (a > 1 -> exp (Q2R x * log a) < exp (Q2R y * log a)) /\
  (a < 1 -> exp (Q2R x * log a) > exp (Q2R y * log a)).
Admitted.

Lemma lemma_22_29_b : forall (a : R) ε,
  a > 0 -> ε > 0 ->
  exists δ, δ > 0 /\ forall x : Q, Rabs (Q2R x) < δ -> Rabs (exp (Q2R x * log a) - 1) < ε.
Admitted.

Lemma lemma_22_29_cd : exists f,
  (forall x : Q, f (Q2R x) = exp (Q2R x * log a)) /\
  continuous f.
Admitted.
