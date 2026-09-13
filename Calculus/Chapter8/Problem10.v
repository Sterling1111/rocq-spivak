From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_10_a : ∀ a x,
  a > 0 -> ∃ k : ℤ, ∃ x', x = k * a + x' /\ 0 <= x' < a.
Proof.
  intros a x H1.
  exists (up (x / a) - 1)%Z, (x - (up (x / a) - 1)%Z * a).
  pose proof archimed (x / a) as [H2 H3].
  rewrite minus_IZR. split; [ring |].
  assert (H4 : x / a * a = x) by (field; lra).
  split; nra.
Qed.

Lemma lemma_8_10_b : ∀ a x (k1 : ℤ) (k2 : ℤ) x1 x2,
  a > 0 -> x = k1 * a + x1 -> 0 <= x1 < a ->
  x = k2 * a + x2 -> 0 <= x2 < a ->
  k1 = k2 /\ x1 = x2.
Proof.
  intros a x k1 k2 x1 x2 H1 H2 H3 H4 H5.
  assert (H6 : k1 = k2).
  { destruct (Z.lt_trichotomy k1 k2) as [H6 | [H6 | H6]]; auto.
    - assert (H7 : (k1 + 1)%Z <= k2) by (apply IZR_le; lia).
      rewrite plus_IZR in H7. nra.
    - assert (H7 : (k2 + 1)%Z <= k1) by (apply IZR_le; lia).
      rewrite plus_IZR in H7. nra. }
  subst. split; [reflexivity | lra].
Qed.
