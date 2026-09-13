From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_20_a : 
  ∃ f : R -> R, ~(∃ c, ∀ x, f x = c) /\ ∀ x y, | f y - f x | <= | y - x |.
Proof.
  exists (λ x, x). split.
  - intros [c H1]. pose proof (H1 0). pose proof (H1 1). lra.
  - intros x y. lra.
Qed.

Lemma lemma_3_20_b : ∀ f : R -> R, 
  (∀ x y, f y - f x <= (y - x)^2) -> ∃ c, ∀ x, f x = c.
Proof.
  intros f H1.
  assert (H2 : ∀ (x h : R) (n : nat), f (x + n * h) - f x <= n * h^2).
  { intros x h n. induction n as [|n IH].
    - simpl. replace (x + 0 * h) with x by ring. lra.
    - rewrite S_INR. pose proof (H1 (x + n * h) (x + (n + 1) * h)) as H2.
      replace (x + (n + 1) * h - (x + n * h)) with h in H2 by ring. nra. }
  assert (H3 : ∀ x y, f y <= f x).
  { intros x y. destruct (Rle_dec (f y) (f x)) as [H3 | H3]; auto.
    pose proof (Rle_0_sqr (y - x)) as H0. unfold Rsqr in H0.
    assert (H4 : 0 < (f y - f x) / ((y - x)^2 + 1)) by (apply Rdiv_pos_pos; nra).
    destruct (archimed_cor1 _ H4) as [n [H5 H6]].
    assert (H7 : 0 < n) by (apply lt_0_INR; exact H6).
    pose proof (H2 x ((y - x) / n) n) as H8.
    replace (x + n * ((y - x) / n)) with y in H8 by (field; lra).
    assert (H9 : n * ((y - x) / n)^2 = (y - x)^2 * / n) by (field; lra).
    rewrite H9 in H8.
    apply (Rmult_lt_compat_r ((y - x)^2 + 1)) in H5; [|nra].
    replace ((f y - f x) / ((y - x)^2 + 1) * ((y - x)^2 + 1)) with (f y - f x) in H5 by (field; nra).
    pose proof (Rinv_0_lt_compat _ H7). nra. }
  exists (f 0). intro x. pose proof (H3 x 0). pose proof (H3 0 x). lra.
Qed.

Lemma lemma_3_20_b_abs : ∀ f : R -> R,
  (∀ x y, f y - f x <= (y - x)^2) ->
  ∀ x y, |f y - f x| <= (y - x)^2.
Proof.
  intros f H1 x y. pose proof (H1 x y). pose proof (H1 y x).
  apply Rabs_le. split; nra.
Qed.
