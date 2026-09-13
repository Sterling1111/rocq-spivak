From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_app_5_a : ∀ f f' a b,
  a < b ->
  ⟦ der ⟧ f (a, b) = f' ->
  convex_on f (a, b) ->
  increasing_on f (a, b) \/ decreasing_on f (a, b) \/
  ∃ c, c ∈ (a, b) /\ decreasing_on f (a, c) /\ increasing_on f (c, b).
Abort.

Lemma lemma_11_app_5_c : ∀ f a b,
  a < b ->
  convex_on f (a, b) ->
  increasing_on f (a, b) \/ decreasing_on f (a, b) \/
  ∃ c, c ∈ (a, b) /\ decreasing_on f (a, c) /\ increasing_on f (c, b).
Abort.
