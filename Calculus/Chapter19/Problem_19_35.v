From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_35 : forall f phi a b,
  a < b ->
  integrable_on a b f ->
  non_decreasing_on phi [a, b] \/ non_increasing_on phi [a, b] ->
  exists xi, xi ∈ [a, b] /\ ∫ a b (f ⋅ phi) = phi a * ∫ a xi f + phi b * ∫ xi b f.
Admitted.
