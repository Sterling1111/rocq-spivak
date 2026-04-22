From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_6_a : ∀ f f' g g' c,
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ g = g' ->
  (∀ x, g x = f x + c) ->
  ∀ x, g' x = f' x.
Proof.
  intros f f' g g' c H1 H2 H3 x.

  assert (H4 : ⟦ der x ⟧ g = f').
  {
    unfold derivative_at.
    apply limit_eq' with (f1 := fun h => (f (x + h) - f x) / h).
    - intros h. repeat rewrite H3. lra.
    - apply H1.
  }
  exact (derivative_at_unique g g' f' x (H2 x) H4).
Qed.

Lemma lemma_9_6_b : ∀ f f' g g' c,
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ g = g' ->
  (∀ x, g x = c * f x) ->
  ∀ x, g' x = c * f' x.
Proof.
  intros f f' g g' c H1 H2 H3 x.
  assert (H4 : ⟦ der x ⟧ g = (fun _ => c * f' x)).
  {
    unfold derivative_at.
    apply limit_eq' with (f1 := fun h => c * ((f (x + h) - f x) / h)).
    - intros h. repeat rewrite H3. lra.
    - apply limit_mult.
      + apply limit_const.
      + apply H1.
  }
  exact (derivative_at_unique g g' (fun _ => c * f' x) x (H2 x) H4).
Qed.