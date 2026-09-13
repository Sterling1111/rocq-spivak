From Calculus.Chapter3 Require Export Prelude.
From Calculus.Chapter3 Require Import Problem16.

Lemma lemma_3_17_a : ∀ f : R -> R,
  (∀ x y, f (x + y) = f x + f y) ->
  (∀ x y, f (x * y) = f x * f y) ->
  (∃ x, f x <> 0) -> f 1 = 1.
Proof.
  intros f H1 H2 [x H3]. pose proof (H2 x 1) as H4.
  rewrite Rmult_1_r in H4. nra.
Qed.

Lemma lemma_3_17_b : ∀ f : R -> R,
  (∀ x y, f (x + y) = f x + f y) ->
  (∀ x y, f (x * y) = f x * f y) ->
  (∃ x, f x <> 0) -> ∀ x, rational x -> f x = x.
Proof.
  intros f H1 H2 H3 x H4.
  destruct (lemma_3_16_b f H1) as [c H5].
  pose proof (lemma_3_17_a f H1 H2 H3) as H6.
  assert (H7 : rational 1) by (apply (IZR_rational 1)).
  pose proof (H5 1 H7). specialize (H5 x H4). nra.
Qed.

Lemma lemma_3_17_c : ∀ f : R -> R,
  (∀ x y, f (x + y) = f x + f y) ->
  (∀ x y, f (x * y) = f x * f y) ->
  (∃ x, f x <> 0) -> ∀ x, x > 0 -> f x > 0.
Proof.
  intros f H1 H2 H3 x H4.
  pose proof (lemma_3_17_a f H1 H2 H3) as H5.
  pose proof (H2 (sqrt x) (sqrt x)) as H6.
  rewrite sqrt_sqrt in H6 by lra.
  pose proof (H2 x (/ x)) as H7.
  rewrite Rinv_r in H7 by lra. rewrite H5 in H7.
  assert (H8 : f x <> 0) by (intro H8; rewrite H8 in H7; lra).
  pose proof (Rle_0_sqr (f (sqrt x))). unfold Rsqr in *. nra.
Qed.

Lemma lemma_3_17_d : ∀ f : R -> R,
  (∀ x y, f (x + y) = f x + f y) ->
  (∀ x y, f (x * y) = f x * f y) ->
  (∃ x, f x <> 0) -> ∀ x y, x > y -> f x > f y.
Proof.
  intros f H1 H2 H3 x y H4.
  pose proof (lemma_3_17_c f H1 H2 H3 (x - y) ltac:(lra)) as H5.
  pose proof (H1 (x - y) y) as H6.
  replace (x - y + y) with x in H6 by lra. lra.
Qed.

Lemma lemma_3_17_e : ∀ f : R -> R,
  (∀ x y, f (x + y) = f x + f y) ->
  (∀ x y, f (x * y) = f x * f y) ->
  (∃ x, f x <> 0) -> ∀ x, f x = x.
Proof.
  intros f H1 H2 H3 x.
  destruct (Rtotal_order (f x) x) as [H4 | [H4 | H4]]; auto.
  - destruct (exists_rational_between (f x) x H4) as [r [[H5 H6] H7]].
    pose proof (lemma_3_17_b f H1 H2 H3 r H7).
    pose proof (lemma_3_17_d f H1 H2 H3 x r ltac:(lra)). lra.
  - destruct (exists_rational_between x (f x) H4) as [r [[H5 H6] H7]].
    pose proof (lemma_3_17_b f H1 H2 H3 r H7).
    pose proof (lemma_3_17_d f H1 H2 H3 r x ltac:(lra)). lra.
Qed.
