From Calculus.Chapter18 Require Import Prelude.

From Calculus.Chapter18 Require Import Problem47.
Import Problem47.GrowthNotations.

Lemma lemma_18_48 : ∀ g : nat -> R -> R,
  (∀ n, continuous (g n)) ->
  (∀ n, limit_pinf_to_pinf (g n)) ->
  ∃ f, continuous f /\ (limit_pinf_to_pinf f) /\ ∀ n, f ≫ g n.
Abort.

Lemma lemma_18_48_general : ∀ g : nat -> R -> R,
  (∀ n, continuous (g n)) ->
  ∃ f, continuous f /\ (∀ x, f x > 0) /\
  ∀ n, limit_pinf_to_pinf (λ x, f x / (1 + |g n x|)).
Abort.
