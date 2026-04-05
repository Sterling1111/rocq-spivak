From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_1_a : forall f f',
  (forall x, f x > 0) ->
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ (log ∘ f) = (fun x => f' x / f x).
Admitted.
