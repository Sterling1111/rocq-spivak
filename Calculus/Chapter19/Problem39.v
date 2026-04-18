From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_39 : forall u v a,
  continuous_on (⟦ der ⟧ u) [a, ∞) ->
  continuous_on (⟦ der ⟧ v) [a, ∞) ->
  converges_improper (fun x => ⟦ der ⟧ u x * v x) a ∞ <->
  converges_improper (fun x => u x * ⟦ der ⟧ v x) a ∞.
Abort.
