From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_29 : forall u v h a b a_bar b_bar,
  a_bar < b_bar ->
  increasing_on h [a_bar, b_bar] ->
  h a_bar = a ->
  h b_bar = b ->
  ∫ a b (fun t => √((⟦ der ⟧ u t)^2 + (⟦ der ⟧ v t)^2)) =
  ∫ a_bar b_bar (fun t => √((⟦ der ⟧ (u ∘ h)%function t)^2 + (⟦ der ⟧ (v ∘ h)%function t)^2)).
Abort.
