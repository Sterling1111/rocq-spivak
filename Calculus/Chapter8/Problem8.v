From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_8_a : ∀ f,
  (∀ a b, a < b -> f a <= f b) ->
  ∀ a, (∃ L, left_limit f a L) /\ (∃ L, right_limit f a L).
Proof. Abort.

Lemma lemma_8_8_b : ∀ f,
  (∀ a b, a < b -> f a <= f b) ->
  ∀ a, (∃ L1 L2, left_limit f a L1 /\ right_limit f a L2 /\ L1 <> L2) \/ continuous_at f a.
Proof. Abort.

Lemma lemma_8_8_c : ∀ f,
  (∀ a b, a < b -> f a <= f b) ->
  (∀ a b y, a < b -> f a < y < f b -> ∃ x, a < x < b /\ f x = y) ->
  continuous f.
Proof. Abort.
