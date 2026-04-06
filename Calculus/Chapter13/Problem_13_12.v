From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_12 : forall f a b c d,
  a < b < c < d ->
  integrable_on a d f ->
  integrable_on b c f.
Proof.
  intros f a b c d H1 H2.
  apply integrable_on_sub_interval_right with (a := a) (c := b); try lra.
  apply integrable_on_sub_interval_left with (b := d) (c := c); try lra.
  exact H2.
Qed.