From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_18_a : ∀ f g f' g',
  (∀ x, g x = (f x)^2) ->
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ g = g' ->
  g' = (λ x, 2 * f x * f' x).
Proof.
  intros f g f' g' H1 H2 H3.
  assert (H4: g = f ⋅ f).
  { extensionality x. rewrite H1. lra. }
  rewrite H4 in H3.
  assert (H5 := derivative_mult f f f' f' H2 H2).
  apply derivative_unique with (f1' := (f' ⋅ f + f ⋅ f')%function) in H3; auto.
  rewrite <- H3.
  extensionality x. lra.
Qed.

Lemma lemma_10_18_b : ∀ f g f' f'' g',
  (∀ x, g x = (f' x)^2) ->
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ f' = f'' ->
  ⟦ der ⟧ g = g' ->
  g' = (λ x, 2 * f' x * f'' x).
Proof.
  intros f g f' f'' g' H1 H2 H3 H4.
  exact (lemma_10_18_a f' g f'' g' H1 H3 H4).
Qed.

Lemma lemma_10_18_c : ∀ f,
  (∀ x, f x > 0) ->
  (∀ x, (⟦ Der x ⟧ f)^2 = f x + 1 / (f x)^3) ->
  ∀ x, ⟦ Der x ⟧ (⟦ Der ⟧ f) = 1 / 2 - 3 / 2 * (1 / (f x)^4).
Proof.
Abort.
