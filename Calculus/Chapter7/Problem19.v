From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_19_a : forall f a b x,
  a < b ->
  continuous_on f [a, b] ->
  exists y, y ∈ [a, b] /\
  forall z, z ∈ [a, b] ->
  (x - y)^2 + (f y)^2 <= (x - z)^2 + (f z)^2.
Proof.
  intros f a b x H1 H2.
  assert (H3 : continuous_on (λ y, (x - y)^2 + (f y)^2) [a, b]).
  {
    apply continuous_on_plus.
    - auto_cont.
    - repeat apply continuous_on_mult; auto; auto_cont.
  }
  pose proof (continuous_on_interval_attains_minimum (λ y, (x - y)^2 + (f y)^2) a b H1 H3) as [y [H4 H5]].
  exists y.
  split; auto.
Qed.