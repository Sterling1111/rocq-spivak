From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_8 : ∀ f g,
  continuous f ->
  continuous g ->
  (f^2 = g^2)%function ->
  (∀ x, f x <> 0) ->
  (∀ x, f x = g x) \/ (∀ x, f x = - g x).
Proof.
  intros f g H1 H2 H3 H4.
  pose proof classic ((∀ x : ℝ, f x = g x) ∨ ∀ x : ℝ, f x = - g x) as [H5 | H5]; auto.
  exfalso.
  apply not_or_and in H5 as [H5 H6].
  apply not_all_ex_not in H5 as [x H7].
  apply not_all_ex_not in H6 as [y H8].

  assert (H9 : ∀ z, f z = g z \/ f z = - g z).
  {
    intros z. apply equal_f with (x := z) in H3.
    simpl in H3. repeat rewrite Rmult_1_r in H3.
    apply Rsqr_eq in H3 as [H3 | H3]; [ left | right ]; solve_R.
  }

  destruct (H9 x) as [H10 | H10]; destruct (H9 y) as [H11 | H11]; try lra.

  assert ((∀ x, f x > 0) \/ (∀ x, f x < 0)) as [H12 | H12].
  {
    pose proof classic ((∀ x0 : ℝ, f x0 > 0) ∨ ∀ x0 : ℝ, f x0 < 0) as [H12 | H12]; auto.
    exfalso.
    apply not_or_and in H12 as [H12 H13].
    apply not_all_ex_not in H12 as [z H12].
    apply not_all_ex_not in H13 as [w H13].
    apply Rnot_gt_le in H12 as [H12 | H12];
    apply Rnot_lt_ge in H13 as [H13 | H13]; 
    try solve [ apply (H4 z); auto | apply (H4 w); auto].

    pose proof intermediate_value_theorem_unordered f z w 0
      ltac:(eapply continuous_imp_continuous_on; eauto) ltac:(solve_R) as [v [H14 H15]].
    apply (H4 v); auto.
  }

  - assert (H13 : g x < 0) by (pose proof (H12 x); lra).
    assert (H14 : g y > 0) by (pose proof (H12 y); lra).
    destruct (intermediate_value_theorem_unordered g x y 0 
      ltac:(eapply continuous_imp_continuous_on; eauto) ltac:(solve_R)) as [c [_ H16]].
    specialize (H9 c). apply (H4 c); lra.
  - assert (H13 : g x > 0) by (pose proof (H12 x); lra).
    assert (H14 : g y < 0) by (pose proof (H12 y); lra).
    destruct (intermediate_value_theorem_unordered g x y 0 
      ltac:(eapply continuous_imp_continuous_on; eauto) ltac:(solve_R)) as [c [_ H16]].
    specialize (H9 c). apply (H4 c); lra.
Qed.