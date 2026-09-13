From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_17_b : ∀ f g a l,
  ⟦ lim a ⟧ f = l ->
  l <> f a ->
  (∀ x, x <> a -> g x = f x) ->
  g a = l ->
  continuous_at g a.
Proof.
  intros f g a l H1 H2 H3 H4. unfold continuous_at.
  rewrite H4. apply limit_eq with (f1 := f).
  - exists 1. split; [solve_R | intros x H5].
    rewrite H3; [reflexivity|solve_R].
  - exact H1.
Qed.

Lemma lemma_6_17_d : ∀ f g,
  (∀ x, ∃ l, ⟦ lim x ⟧ f = l) ->
  (∀ x, ⟦ lim x ⟧ f = g x) ->
  continuous g.
Proof.
  intros f g H1 H2 a ε H3.
  destruct (H2 a (ε/2) ltac:(lra)) as [δ [H4 H5]].
  exists (δ/2). split; [lra | intros x H6].
  assert (H7 : |g x - g a| <= ε/2).
  {
    apply Rnot_lt_le. intros H7.
    destruct (H2 x (|g x - g a| - ε/2) ltac:(lra)) as [δ' [H8 H9]].
    set (d := Rmin δ' (Rmin (δ/2) (|x - a|)) / 2).
    specialize (H5 (x + d) ltac:(unfold d; solve_R)).
    specialize (H9 (x + d) ltac:(unfold d; solve_R)).
    solve_R.
  }
  lra.
Qed.
