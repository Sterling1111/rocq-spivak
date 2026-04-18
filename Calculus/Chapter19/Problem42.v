From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_42 : forall f,
  converges_improper f 0 ∞ -> exists L, limit_at_infinity (fun x => ∫ 0 x f) L.
Abort.
