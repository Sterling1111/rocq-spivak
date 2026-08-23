From Calculus.Chapter14 Require Import Prelude.

Lemma lemma_14_1_i' : forall a,
  let F := λ x, ∫ a (x^3) (λ t, (sin t)^3) in
  ⟦ der ⟧ F = (λ x, 3 * x^2 * (sin (x^3))^3).
Proof.
  intros a F.
  set (G := λ u, ∫ a u (λ t, (sin t)^3)).

  assert (H1 : ⟦ der ⟧ G = (λ u, (sin u)^3)).
  { unfold G. apply FTC1_global. auto_cont. }

  change (⟦ der ⟧ (G ∘ (λ x, x^3)) = (λ x, 3 * x^2 * (sin (x^3))^3)).

  replace (λ x, 3 * x^2 * (sin (x^3))^3) with (((λ u, (sin u)^3) ∘ (λ x, x^3)) ⋅ (λ x, 3 * x^2)).
  2 : { extensionality x. unfold compose. ring. }

  apply derivative_comp.
  - auto_diff.
  - exact H1.
Qed.

Lemma lemma_14_1_ii : forall x,
  ⟦ der x ⟧ (λ x, ∫ 3 (∫ 1 x (λ t, (sin t)^3)) (λ t, 1 / (1 + (sin t)^6 + t^2))) =
    (λ x, (sin x)^3 / (1 + (sin (∫ 1 x (λ t, (sin t)^3)))^6 + (∫ 1 x (λ t, (sin t)^3))^2)).
Proof.
  intros x.
  set (G := λ x, ∫ 1 x (λ t, (sin t)^3)).
  set (H := λ u, ∫ 3 u (λ t, 1 / (1 + (sin t)^6 + t^2))).

  assert (H1 : ⟦ der ⟧ G = (λ x, (sin x)^3)).
  { unfold G. apply FTC1_global. auto_cont. }

  assert (H2 : ⟦ der ⟧ H = (λ u, 1 / (1 + (sin u)^6 + u^2))).
  { unfold H. apply FTC1_global. auto_cont. }

  change (⟦ der x ⟧ (H ∘ G) = (λ x, (sin x)^3 / (1 + (sin (G x))^6 + (G x)^2))).

  replace (λ x, (sin x)^3 / (1 + (sin (G x))^6 + (G x)^2)) with
    (((λ u, 1 / (1 + (sin u)^6 + u^2)) ∘ G) ⋅ (λ x, (sin x)^3)).
  2 : { extensionality y. unfold compose. lra. }

  apply derivative_at_comp.
  - apply H1.
  - apply H2.
Qed.

Lemma lemma_14_1_iii : forall x,
  ⟦ der x ⟧ (λ x, ∫ 15 x (λ y, ∫ 8 y (λ t, 1 / (1 + t^2 + (sin t)^2)))) =
    (λ x, ∫ 8 x (λ t, 1 / (1 + t^2 + (sin t)^2))).
Proof.
  intros x.
  set (G := λ y, ∫ 8 y (λ t, 1 / (1 + t^2 + (sin t)^2))).

  assert (H1 : ⟦ der ⟧ G = (λ y, 1 / (1 + y^2 + (sin y)^2))).
  { unfold G. apply FTC1_global. auto_cont. }

  assert (H2 : continuous G).
  {
    apply differentiable_imp_continuous.
    apply derivative_imp_differentiable with
      (f' := λ y, 1 / (1 + y^2 + (sin y)^2)).
    exact H1.
  }

  change (⟦ der x ⟧ (λ x, ∫ 15 x G) = G).
  exact ((FTC1_global G 15 H2) x).
Qed.

Lemma lemma_14_1_iv : forall b x,
  ⟦ der x ⟧ (λ x, ∫ x b (λ t, 1 / (1 + t^2 + (sin t)^2))) =
    (λ x, - (1 / (1 + x^2 + (sin x)^2))).
Proof.
  intros b x.
  set (G := λ x, ∫ x b (λ t, 1 / (1 + t^2 + (sin t)^2))).
  set (g := λ x, 1 / (1 + x^2 + (sin x)^2)).

  assert (H1 : ⟦ der ⟧ G = (-g)%function).
  { unfold G, g. apply FTC1'_global. auto_cont. }

  change (⟦ der x ⟧ G = (-g)%function).
  exact (H1 x).
Qed.

Lemma lemma_14_1_v : forall a b,
  a < b ->
  ⟦ der ⟧ (λ x, ∫ a b (λ t, x / (1 + t^2 + (sin t)^2))) =
    (λ x, ∫ a b (λ t, 1 / (1 + t^2 + (sin t)^2))).
Proof.
  intros a b H1.
  set (g := λ t, 1 / (1 + t^2 + (sin t)^2)).

  assert (H2 : integrable_on a b g).
  { apply theorem_13_3; auto; try lra. unfold g. auto_cont. }

  change (⟦ der ⟧ (λ x, ∫ a b (λ t, x / (1 + t^2 + (sin t)^2))) =
    (λ x, ∫ a b g)).

  replace (λ x, ∫ a b (λ t, x / (1 + t^2 + (sin t)^2))) with
    (λ x, x * ∫ a b g).
  2 : {
    extensionality x.
    replace (λ t, x / (1 + t^2 + (sin t)^2)) with (λ t, x * g t).
    2 : { extensionality t. unfold g. lra. }
    rewrite integral_mult_scalar; auto.
  }

  auto_diff.
Qed.

Lemma lemma_14_1_vi : forall x,
  ⟦ der x ⟧ (λ x, sin (∫ 0 x (λ y, sin (∫ 0 y (λ t, (sin t)^3))))) =
    (λ x, cos (∫ 0 x (λ y, sin (∫ 0 y (λ t, (sin t)^3)))) *
              sin (∫ 0 x (λ t, (sin t)^3))).
Proof.
  intros x.
  set (G := λ y, ∫ 0 y (λ t, (sin t)^3)).
  set (H := λ x, ∫ 0 x (λ y, sin (G y))).

  assert (H1 : ⟦ der ⟧ G = (λ y, (sin y)^3)).
  { unfold G. apply FTC1_global. auto_cont. }

  assert (H2 : continuous G).
  {
    apply differentiable_imp_continuous.
    apply derivative_imp_differentiable with (f' := λ y, (sin y)^3).
    exact H1.
  }

  assert (H3 : continuous (λ y, sin (G y))).
  {
    change (continuous (sin ∘ G)).
    apply continuous_comp.
    - exact H2.
    - auto_cont.
  }

  assert (H4 : ⟦ der ⟧ H = (λ x, sin (G x))).
  { unfold H. apply FTC1_global. exact H3. }

  change (⟦ der x ⟧ (sin ∘ H) = (λ x, cos (H x) * sin (G x))).

  replace (λ x, cos (H x) * sin (G x)) with
    ((cos ∘ H) ⋅ (λ x, sin (G x))).
  2 : { extensionality y. unfold compose. reflexivity. }

  apply derivative_at_comp.
  - apply H4.
  - auto_diff.
Qed.

Lemma lemma_14_1_vii : forall F F_inv,
  (forall x, x > 0 ->
    F x = ∫ 1 x (λ t, 1 / t)) ->
  inverse_on F F_inv (0, ∞) ℝ ->
  ⟦ der ⟧ F_inv = (λ y, F_inv y).
Proof.
Abort.

Lemma lemma_14_1_viii : forall F F_inv,
  (forall x, -1 < x < 1 ->
    F x = ∫ 0 x (λ t, 1 / √(1 - t^2))) ->
  inverse_on F F_inv (-1, 1) (-π/2, π/2) ->
  ⟦ der ⟧ F_inv (-π/2, π/2) =
    (λ y, √(1 - (F_inv y)^2)).
Proof.
Abort.