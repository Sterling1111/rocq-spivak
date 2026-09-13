From Calculus.Chapter21 Require Import Prelude.

Definition local_max (f : R -> R) (x : R) : Prop :=
  ∃ δ : R, δ > 0 /\ ∀ y, |y - x| < δ -> f y <= f x.

Definition local_min (f : R -> R) (x : R) : Prop :=
  ∃ δ : R, δ > 0 /\ ∀ y, |y - x| < δ -> f y >= f x.

Lemma lemma_21_8_a : ∀ f,
  (∀ x, local_max f x) ->
  countable (image f).
Abort.

Lemma lemma_21_8_b : ∀ f,
  continuous f ->
  (∀ x, local_max f x) ->
  ∃ c, ∀ x, f x = c.
Abort.

Lemma lemma_21_8_c : ∀ f,
  (∀ x, local_min f x) ->
  countable (image f).
Abort.

Lemma lemma_21_8_c' : ∀ f,
  continuous f ->
  (∀ x, local_min f x) ->
  ∃ c, ∀ x, f x = c.
Abort.
