From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_21 : forall n f a,
  limit_at_point (fun x => (f x - P(n, a, f) x) / (x - a)^n) a 0.
Admitted.
