From Calculus.Chapter15 Require Import Prelude.

Lemma lemma_15_22 : ∀ x y,
  x^2 + y^2 = 1 ->
  ∃ θ, x = cos θ /\ y = sin θ.
Proof.
  intros x y H1.
  assert (H2 : x ∈ [-1, 1]) by (split; nra).
  pose proof arccos_spec as [H3 [H4 [H5 H6]]].
  pose proof H4 x H2 as H7.
  pose proof H6 x H2 as H8.
  pose proof pythagorean_identity (arccos x) as H9.
  assert (H10 : 0 <= sin (arccos x)).
  { destruct H7 as [H7 H11].
    destruct (Req_dec (arccos x) 0) as [H12 | H12].
    - rewrite H12, sin_0. lra.
    - destruct (Req_dec (arccos x) π) as [H13 | H13].
      + rewrite H13, sin_π. lra.
      + pose proof sin_gt_0 (arccos x) ltac:(lra). lra. }
  destruct (Rle_dec 0 y) as [H11 | H11].
  - exists (arccos x). split; [symmetry; exact H8 | nra].
  - exists (- arccos x). rewrite cos_even_odd, sin_even_odd.
    split; [symmetry; exact H8 | nra].
Qed.
