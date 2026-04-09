From Calculus.Chapter8 Require Import Prelude.

Definition shadow_point (f : R -> R) (x : R) :=
  ∃ y, y > x /\ f y > f x.

Lemma lemma_8_20_a : ∀ f a b,
  continuous f ->
  (∀ x, a < x < b -> shadow_point f x) ->
  ~ shadow_point f a ->
  ~ shadow_point f b ->
  f a > f b ->
  ∀ x, a <= x <= b -> f x <= f a.
Proof. Admitted.

Lemma lemma_8_20_b : ∀ f a b,
  continuous f ->
  a < b ->
  (∀ x, a < x < b -> shadow_point f x) ->
  ~ shadow_point f a ->
  ~ shadow_point f b ->
  f a = f b.
Proof. Admitted.
