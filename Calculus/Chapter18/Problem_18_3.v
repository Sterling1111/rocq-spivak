From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_3_interval : ∀ f f' a b,
  a < b ->
  (∀ x, x ∈ [a, b] -> f x > 0) ->
  continuous_on (fun t => f' t / f t) [a, b] ->
  ⟦ der ⟧ f = f' ->
  ∫ a b (fun t => f' t / f t) = log (f b) - log (f a).
Proof.
  intros f f' a b H1 H2 H3 H4.
  apply FTC2 with (g := fun t => log (f t)); auto.
  auto_diff.
Qed.