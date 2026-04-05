From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_17_a : forall a L,
  ⟦ lim ⟧ (fun n => a (n + 1)%nat - a n) = L ->
  ⟦ lim ⟧ (fun n => a n / INR n) = L.
Admitted.

Lemma lemma_22_17_b : forall f L,
  continuous f ->
  limit_pinf (fun x => f (x + 1) - f x) L ->
  limit_pinf (fun x => f x / x) L.
Admitted.
