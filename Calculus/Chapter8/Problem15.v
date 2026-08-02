From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_15 : ∀ f a b,
  a < b ->
  continuous_on f [a, b] ->
  f a < 0 < f b ->
  f ((a + b) / 2) = 0 \/
  (f a < 0 < f ((a + b) / 2)) \/
  (f ((a + b) / 2) < 0 < f b).
Proof.
  intros f a b H1 H2 [H3 H4].
  destruct (Req_dec (f ((a + b) / 2)) 0) as [H5 | H5].
  - left. exact H5.
  - destruct (Rlt_dec (f ((a + b) / 2)) 0) as [H7 | H7].
    + right. right. split; auto.
    + right. left. split; lra.
Qed.