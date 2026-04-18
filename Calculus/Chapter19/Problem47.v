From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_47 : forall f a b P,
  continuous_on (⟦ der ⟧ (⟦ der ⟧ f)) [a, b] ->
  (forall x, x ∈ [a, b] -> P x = f x) ->
  exists c, P c = f c.
Abort.
