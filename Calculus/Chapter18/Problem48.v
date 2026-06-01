From Calculus.Chapter18 Require Import Prelude.
From Calculus.Chapter18 Require Import Problem47.

Import Problem47.GrowthNotations.

Lemma lemma_18_48 : ∀ (l : list (ℝ -> ℝ)),
  Forall continuous l ->
  ∃ f, continuous f /\ Forall (λ g, f ≫ g) l.
Proof.
Abort.