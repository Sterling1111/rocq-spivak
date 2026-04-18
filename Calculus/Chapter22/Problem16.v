From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_16 : forall a L,
  ⟦ lim ⟧ a = L ->
  ⟦ lim ⟧ (fun n => (∑ 1 n a) / INR n) = L.
Abort.
