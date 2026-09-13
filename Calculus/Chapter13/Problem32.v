From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_32_a : ∀ f a b,
  a < b ->
  continuous_on f [a, b] ->
  (∀ g, continuous_on g [a, b] -> ∫ a b (f ⋅ g) = 0) ->
  ∀ x, x ∈ [a, b] -> f x = 0.
Proof.
  intros f a b H1 H2 H3 x H4.
  specialize (H3 f H2).
  assert (H5 : continuous_on (f ⋅ f) [a, b]) by (apply continuous_on_mult; auto).
  destruct (Req_dec (f x) 0) as [H6 | H6]; auto.
  assert (H7 : 0 < ∫ a b (f ⋅ f)).
  {
    apply integral_pos'; auto.
    - intros y H7. change (0 <= f y * f y). nra.
    - exists x. split; auto. change (f x * f x > 0). nra.
  }
  lra.
Qed.

Lemma lemma_13_32_b : ∀ f a b,
  a < b ->
  continuous_on f [a, b] ->
  (∀ g, continuous_on g [a, b] -> g a = 0 -> g b = 0 -> ∫ a b (f ⋅ g) = 0) ->
  ∀ x, x ∈ [a, b] -> f x = 0.
Proof.
  intros f a b H1 H2 H3.
  set (h := λ x, f x * ((x-a)*(b-x))).
  assert (H4 : continuous_on h [a, b]).
  { unfold h. apply continuous_on_mult; auto. auto_cont. }
  assert (H5 : ∀ k, continuous_on k [a, b] -> ∫ a b (h ⋅ k) = 0).
  {
    intros k H5.
    replace (h ⋅ k) with (f ⋅ (λ x, ((x-a)*(b-x))*k x))
      by (extensionality x; unfold h; ring).
    apply H3; try (cbn; ring).
    apply continuous_on_mult; auto. auto_cont.
  }
  pose proof lemma_13_32_a h a b H1 H4 H5 as H6.
  assert (H7 : ∀ x, x ∈ (a, b) -> f x = 0).
  {
    intros x H7. specialize (H6 x ltac:(solve_R)). unfold h in H6.
    assert (H8 : 0 < (x-a)*(b-x)) by (apply Rmult_lt_0_compat; solve_R).
    nra.
  }
  apply continuous_on_closed_interval_iff in H2 as [H8 [H9 H10]]; auto.
  intros x H11. destruct (Req_dec x a) as [H12 | H12].
  - subst x. apply limit_right_unique with (f := f) (a := a); auto.
    apply limit_right_eq with (f1 := λ _, 0).
    + exists (b-a). split; [lra |]. intros x H12. symmetry. apply H7. solve_R.
    + apply limit_right_const.
  - destruct (Req_dec x b) as [H13 | H13].
    + subst x. apply limit_left_unique with (f := f) (a := b); auto.
      apply limit_left_eq with (f1 := λ _, 0).
      * exists (b-a). split; [lra |]. intros x H13. symmetry. apply H7. solve_R.
      * apply limit_left_const.
    + apply H7. solve_R.
Qed.
