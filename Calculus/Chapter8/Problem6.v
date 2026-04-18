From Calculus.Chapter8 Require Import Prelude.

Definition dense (A : Ensemble ℝ) :=
  ∀ x y : ℝ, x < y -> ∃ z, z ∈ A /\ z ∈ (x, y).

Lemma lemma_8_6_a : ∀ f A,
  continuous f -> dense A -> (∀ x, x ∈ A -> f x = 0) -> ∀ x, f x = 0.
Proof. Abort.

Lemma lemma_8_6_b : ∀ f g A,
  continuous f -> continuous g -> dense A -> (∀ x, x ∈ A -> f x = g x) -> ∀ x, f x = g x.
Proof. Abort.

Lemma lemma_8_6_c : ∀ f g A,
  continuous f -> continuous g -> dense A -> (∀ x, x ∈ A -> f x >= g x) -> ∀ x, f x >= g x.
Proof. Abort.
