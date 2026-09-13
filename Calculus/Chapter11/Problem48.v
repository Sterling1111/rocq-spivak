From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_48 : ∀ f f' a b L1 L2,
  a < b ->
  continuous_on f (a, b) ->
  ⟦ der ⟧ f (a, b) = f' ->
  ⟦ lim a⁺ ⟧ f = L1 ->
  ⟦ lim b⁻ ⟧ f = L2 ->
  ∃ x, x ∈ (a, b) /\ f' x = (L2 - L1) / (b - a).
Proof.
  intros f f' a b L1 L2 H1 H2 H3 H4 H5.
  set (g := λ x, if Req_dec_T x a then L1 else if Req_dec_T x b then L2 else f x).
  assert (H6 : g a = L1 /\ g b = L2).
  { unfold g. destruct (Req_dec_T a a), (Req_dec_T b a), (Req_dec_T b b); split; solve_R. }
  assert (H7 : ∀ x, x ∈ (a, b) -> g x = f x).
  { intros x H7. unfold g. destruct (Req_dec_T x a), (Req_dec_T x b); solve_R. }
  assert (H8 : ⟦ der ⟧ g (a, b) = f').
  { apply derivative_on_eq with (f1 := f); auto. intros x H8. symmetry. apply H7; auto. }
  assert (H9 : continuous_on g [a, b]).
  {
    apply continuous_on_closed_interval_iff; auto. repeat split.
    - intros x H9. apply differentiable_at_imp_continuous_at.
      apply derivative_at_imp_differentiable_at with (f' := f').
      apply derivative_on_imp_derivative_at with (D := (a, b)); auto_interval.
    - unfold continuous_at_right. rewrite (proj1 H6).
      apply limit_right_eq with (f1 := f); auto.
      exists (b - a). split; [lra |]. intros x H9. symmetry. apply H7. solve_R.
    - unfold continuous_at_left. rewrite (proj2 H6).
      apply limit_left_eq with (f1 := f); auto.
      exists (b - a). split; [lra |]. intros x H9. symmetry. apply H7. solve_R.
  }
  pose proof mean_value_theorem g a b H1 H9
    ltac:(apply derivative_on_imp_differentiable_on with (f' := f'); auto) as [x [H10 H11]].
  pose proof derivative_on_imp_derivative_at g f' (a, b) x ltac:(auto_interval) H8 as H12.
  pose proof derivative_at_unique g _ _ x H12 H11 as H13.
  exists x. split; auto. simpl in H13. rewrite (proj1 H6), (proj2 H6) in H13. exact H13.
Qed.
