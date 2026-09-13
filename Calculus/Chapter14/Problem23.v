From Calculus.Chapter14 Require Import Prelude.

Lemma lemma_14_23_a : ∀ f g F G y y',
  ⟦ der ⟧ F = f ->
  ⟦ der ⟧ G = g ->
  ⟦ der ⟧ y = y' ->
  (∀ x, g (y x) * y' x = f x) ->
  ∃ c, ∀ x, G (y x) = F x + c.
Proof.
  intros f g F G y y' H1 H2 H3 H4.
  assert (H5 : ⟦ der ⟧ (λ x, G (y x) - F x) = (λ _, 0)).
  {
    apply derivative_ext with (f1' := λ x, g (y x) * y' x - f x).
    - intros x. rewrite H4. lra.
    - auto_diff.
  }
  pose proof derivative_zero_imp_const' _ H5 as [c H6].
  exists c. intros x. specialize (H6 x). lra.
Qed.

Lemma lemma_14_23_b : ∀ f g F G y y' c,
  ⟦ der ⟧ F = f ->
  ⟦ der ⟧ G = g ->
  ⟦ der ⟧ y = y' ->
  (∀ x, G (y x) = F x + c) ->
  ∀ x, g (y x) * y' x = f x.
Proof.
  intros f g F G y y' c H1 H2 H3 H4 x.
  assert (H5 : ⟦ der ⟧ (λ x, G (y x)) = (λ x, g (y x) * y' x)) by auto_diff.
  assert (H6 : ⟦ der ⟧ (λ x, G (y x)) = f).
  {
    apply derivative_eq with (f1 := λ x, F x + c).
    - intros t. symmetry. apply H4.
    - auto_diff.
  }
  exact (derivative_at_unique _ _ _ x (H5 x) (H6 x)).
Qed.

Lemma lemma_14_23_c : ∀ y y',
  ⟦ der ⟧ y = y' ->
  (∀ x, y' x = (1 + x^2) / (1 + y x)) ->
  ∃ c, ∀ x, y x + (y x)^2 / 2 = x + x^3 / 3 + c.
Abort.

Lemma lemma_14_23_d : ∀ y y',
  ⟦ der ⟧ y = y' ->
  (∀ x, y' x = -1 / (1 + 5 * (y x)^4)) ->
  ∃ c, ∀ x, y x + (y x)^5 = -x + c.
Proof.
  intros y y' H1 H2.
  apply lemma_14_23_a with (f := λ _, -1) (g := λ t, 1 + 5 * t^4)
    (F := λ x, -x) (G := λ t, t + t^5) (y' := y');
    [auto_diff | auto_diff | exact H1 |].
  intros x. rewrite H2. field. solve_R.
Qed.

Lemma lemma_14_23_e : ∀ y y',
  ⟦ der ⟧ y = y' ->
  (∀ x, y x * y' x = - x) ->
  ∃ c, ∀ x, (y x)^2 = -x^2 + c.
Proof.
  intros y y' H1 H2.
  apply lemma_14_23_a with (f := λ x, -2 * x) (g := λ t, 2 * t)
    (F := λ x, -x^2) (G := λ t, t^2) (y' := y');
    [auto_diff | auto_diff | exact H1 |].
  intros x. specialize (H2 x). lra.
Qed.

Lemma lemma_14_23_e' : ∀ y y',
  ⟦ der ⟧ y = y' ->
  (∀ x, y x * y' x = - x) ->
  y 0 = -1 ->
  ∀ x, (y x)^2 = 1 - x^2.
Proof.
  intros y y' H1 H2 H3 x.
  pose proof lemma_14_23_e y y' H1 H2 as [c H4].
  pose proof H4 0 as H5. rewrite H3 in H5.
  specialize (H4 x). nra.
Qed.
