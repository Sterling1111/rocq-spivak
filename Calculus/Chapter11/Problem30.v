From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_30_a : forall f g f' g' a x,
  ⟦ der ⟧ f = f' -> 
  ⟦ der ⟧ g = g' ->
  (∀ x, f' x > g' x) ->
  f a = g a ->
  (x > a -> f x > g x) /\ (x < a -> f x < g x).
Proof.
  intros f g f' g' a x H1 H2 H3 H4.
  set (h := (f - g)%function).
  assert (forall u v, u < v -> continuous_on h [u, v]) as H5.
  {
    intros u v H6.
    apply continuous_imp_continuous_on, differentiable_imp_continuous, 
    derivative_imp_differentiable with (f' := (f' - g')%function).
    unfold h; auto_diff.
  }
  assert (forall u v, u < v -> differentiable_on h (u, v)) as H6.
  {
    intros u v H7.
    apply differentiable_imp_differentiable_on.
    - unfold h; apply derivative_imp_differentiable with (f' := (f' - g')%function); auto_diff.
    - apply differentiable_domain_open, H7.
  }
  split; intros H7.
  - pose proof mean_value_theorem h a x H7 (H5 a x H7) (H6 a x H7) as [y [H8 H9]].
    assert (⟦ der y ⟧ h = f' - g') as H10 by (unfold h; auto_diff).
    pose proof derivative_at_unique h (λ _ : ℝ, (h x - h a) / (x - a)) (f' - g') y H9 H10 as H11.
    simpl in H11; unfold h in *.
    rewrite H4 in H11.
    apply Rmult_eq_compat_r with (r := (x - a)) in H11.
    field_simplify in H11; try lra.
    specialize (H3 y).
    nra.
  - pose proof mean_value_theorem h x a H7 (H5 x a H7) (H6 x a H7) as [y [H8 H9]].
    assert (⟦ der y ⟧ h = f' - g') as H10 by (unfold h; auto_diff).
    pose proof derivative_at_unique h (λ _ : ℝ, (h a - h x) / (a - x)) (f' - g') y H9 H10 as H11.
    simpl in H11; unfold h in *.
    rewrite <- H4 in H11.
    apply Rmult_eq_compat_r with (r := (a - x)) in H11.
    field_simplify in H11; try lra.
    specialize (H3 y).
    nra.
Qed.

Lemma lemma_11_30_a' : forall f g f' g' a x,
  ⟦ der ⟧ f = f' -> 
  ⟦ der ⟧ g = g' ->
  f a = g a ->
  (forall c, (c ∈ (a, x) \/ c ∈ (x, a)) -> f' c > g' c) ->
  (x > a -> f x > g x) /\ (x < a -> f x < g x).
Proof.
  intros f g f' g' a x H1 H2 H3 H4.
  set (h := (f - g)%function).
  assert (H5 : forall u v, u < v -> continuous_on h [u, v]).
  {
    intros u v H5.
    apply continuous_imp_continuous_on, differentiable_imp_continuous, 
    derivative_imp_differentiable with (f' := (f' - g')%function).
    unfold h; apply derivative_minus; auto.
  }
  assert (H6 : forall u v, u < v -> differentiable_on h (u, v)).
  {
    intros u v H6.
    apply differentiable_imp_differentiable_on.
    - unfold h; apply derivative_imp_differentiable with (f' := (f' - g')%function).
      apply derivative_minus; auto.
    - apply differentiable_domain_open; lra.
  }
  split; intros H7.
  - pose proof mean_value_theorem h a x H7 (H5 a x H7) (H6 a x H7) as [y [H8 H9]].
    assert (H10 : ⟦ der y ⟧ h = (f' - g')%function).
    { unfold h; apply derivative_at_minus; auto. }
    pose proof derivative_at_unique h (fun _ => (h x - h a) / (x - a)) (f' - g')%function y H9 H10 as H11.
    simpl in H11; unfold h in H11.
    rewrite H3 in H11.
    apply Rmult_eq_compat_r with (r := x - a) in H11.
    field_simplify in H11; try lra.
    assert (H12 : y ∈ (a, x) \/ y ∈ (x, a)) by solve_R.
    specialize (H4 y H12).
    nra.
  - pose proof mean_value_theorem h x a H7 (H5 x a H7) (H6 x a H7) as [y [H8 H9]].
    assert (H10 : ⟦ der y ⟧ h = (f' - g')%function).
    { unfold h; apply derivative_at_minus; auto. }
    pose proof derivative_at_unique h (fun _ => (h a - h x) / (a - x)) (f' - g')%function y H9 H10 as H11.
    simpl in H11; unfold h in H11.
    rewrite H3 in H11.
    apply Rmult_eq_compat_r with (r := a - x) in H11.
    field_simplify in H11; try lra.
    assert (H12 : y ∈ (a, x) \/ y ∈ (x, a)) by solve_R.
    specialize (H4 y H12).
    nra.
Qed.

Lemma lemma_11_30_b : ∃ f g f' g' a x,
  ⟦ der ⟧ f = f' /\
  ⟦ der ⟧ g = g' /\
  (∀ x, f' x > g' x) /\
  f a <> g a /\
  ~ ((x > a -> f x > g x) /\ (x < a -> f x < g x)).
Proof.
  exists (λ x, x), (λ _, 1), (λ _, 1), (λ _, 0), 0, 0.5.
  repeat split.
  - auto_diff.
  - auto_diff.
  - intros _. lra.
  - lra.
  - intros [H1 _].
    specialize (H1 ltac:(lra)).
    lra.
Qed.

Lemma lemma_11_30_c : forall f g f' g' a x0 x,
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ g = g' ->
  f a = g a ->
  (∀ x, f' x >= g' x) ->
  x0 > a ->
  f' x0 > g' x0 ->
  x >= x0 ->
  f x > g x.
Proof.
  intros f g f' g' a x0 x H1 H2 H3 H4 H5 H6 H7.
  set (h := (f - g)%function).
  set (h' := (f' - g')%function).
  assert (forall u v, u < v -> continuous_on h [u, v]) as H8.
  {
    intros u v H8.
    apply continuous_imp_continuous_on, differentiable_imp_continuous, 
    derivative_imp_differentiable with (f' := h').
    unfold h, h'; apply derivative_minus; auto.
  }
  assert (forall u v, u < v -> differentiable_on h (u, v)) as H9.
  {
    intros u v H9.
    apply differentiable_imp_differentiable_on.
    - unfold h, h'; apply derivative_imp_differentiable with (f' := h'); apply derivative_minus; auto.
    - apply differentiable_domain_open, H9.
  }
  assert (non_decreasing h) as H10.
  {
    apply derivative_nonneg_imp_nondecreasing with (f' := h').
    - unfold h, h'; apply derivative_minus; auto.
    - intros y. unfold h'. specialize (H4 y). lra.
  }
  assert (h a = 0) as H11 by (unfold h; lra).
  assert (h x0 > 0) as H12.
  {
    assert (h a <= h x0) as H12 by (apply H10; try apply Full_intro; solve_R).
    assert (h x0 = 0 \/ h x0 > 0) as [H13 | H13] by lra.
    2: { exact H13. }
    assert (⟦ der x0 ⁻ ⟧ h = (fun _ => 0)) as H14.
    {
      apply derivative_at_left_eq with (f1 := fun _ => 0).
      - exists (x0 - a). split; [lra |].
        intros y H14.
        assert (h a <= h y) as H15 by (apply H10; try apply Full_intro; solve_R).
        assert (y = x0 \/ y < x0) as [H16 | H16] by lra.
        + subst y; lra.
        + assert (h y <= h x0) as H17 by (apply H10; try apply Full_intro; solve_R).
          lra.
      - apply derivative_at_left_const.
    }
    assert (⟦ der x0 ⟧ h = h') as H15.
    { unfold h, h'. apply derivative_at_minus; [apply H1 | apply H2]. }
    apply derivative_at_iff in H15 as [_ H15].
    pose proof derivative_at_left_unique h (fun _ => 0) h' x0 H14 H15 as H16.
    simpl in H16. unfold h' in H16. lra.
  }
  assert (x0 = x \/ x0 < x) as [H13 | H13] by lra.
  - subst x. unfold h in H12. lra.
  - assert (h x0 <= h x) as H14 by (apply H10; try apply Full_intro; solve_R).
    unfold h in *. lra.
Qed.