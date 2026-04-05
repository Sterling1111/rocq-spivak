From Calculus.Chapter15 Require Import Prelude.

(* Problem 32: Sturm comparison theorem *)

(* (c) If φ₁'' + g₁φ₁ = 0, φ₂'' + g₂φ₂ = 0, g₂ > g₁,
       and φ₂ does not vanish on (a,b), then φ₁ cannot vanish
       at both a and b. *)
Lemma lemma_15_32_c : forall φ₁ φ₂ g₁ g₂ a b,
  a < b ->
  (forall x, x ∈ (a, b) -> g₂ x > g₁ x) ->
  (forall x, ⟦ der x ⟧ (⟦ Der ⟧ φ₁) = (fun x => - g₁ x * φ₁ x)) ->
  (forall x, ⟦ der x ⟧ (⟦ Der ⟧ φ₂) = (fun x => - g₂ x * φ₂ x)) ->
  (forall x, x ∈ (a, b) -> φ₂ x <> 0) ->
  ~ (φ₁ a = 0 /\ φ₁ b = 0).
Admitted.
