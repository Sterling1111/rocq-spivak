From Calculus.Chapter19 Require Import Prelude.

(* Problem 3: Integration by parts. *)

Lemma lemma_19_3_ibp : forall f g a b,
  a < b ->
  continuous_on (⟦ der ⟧ f) [a, b] ->
  continuous_on (⟦ der ⟧ g) [a, b] ->
  ∫ a b (fun x => f x * ⟦ der ⟧ g x) =
    f b * g b - f a * g a - ∫ a b (fun x => ⟦ der ⟧ f x * g x).
Admitted.
