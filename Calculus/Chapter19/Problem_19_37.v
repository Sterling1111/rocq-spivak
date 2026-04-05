From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_37 : forall f a,
  a > 0 ->
  converges_improper (fun x => f x) a ∞ ->
  exists L, limit_at_infinity (fun b => ∫ a b f) L.
Admitted.
