From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_45 : forall f,
  differentiable f ->
  limit_at_point (fun x => (f x)^(1/x)) 0 (exp (⟦ der ⟧ f 0)).
Abort.
