From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_19 : forall f g a n,
  nth_differentiable_at n f a ->
  nth_differentiable_at n g a ->
  equal_up_to_order n (f ⋅ g) (fun x => P(n, a, f) x * P(n, a, g) x) a.
Admitted.
