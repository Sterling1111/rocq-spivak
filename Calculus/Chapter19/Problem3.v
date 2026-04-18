From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_3_ibp : forall f g a b,
  a < b ->
  continuous_on (⟦ Der ⟧ f) [a, b] ->
  continuous_on (⟦ Der ⟧ g) [a, b] ->
  ∫ a b (fun x => f x * (⟦ Der ⟧ g) x) =
    f b * g b - f a * g a - ∫ a b (fun x => (⟦ Der ⟧ f) x * g x).
Proof.
  intros f g a b H1 H2 H3.
Abort.
