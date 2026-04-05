From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_39 : forall f a,
  limit_at_point (fun x => (f x)^a) 0 1.
Admitted.
