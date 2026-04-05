From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_44 : forall x,
  limit_at_point (fun n => (1 + x/n)^n) 0 (exp x).
Admitted.
