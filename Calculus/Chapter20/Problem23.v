From Calculus.Chapter20 Require Import Prelude.

Definition schwarz_second_derivative (f : ℝ -> ℝ) (a L : ℝ) : Prop :=
  ⟦ lim 0 ⟧ (λ h, (f (a+h) + f (a-h) - 2*f a) / h^2) = L.

Lemma lemma_20_23_a : ∀ f a,
  nth_differentiable_at 2 f a -> schwarz_second_derivative f a (⟦ Der ^ 2 a ⟧ f).
Proof.
  intros f a H1.
  pose proof (theorem_20_1 2 a f ltac:(lia) H1) as H2.
  set (g := λ x, R(2,a,f) x / (x-a)^2).
  assert (H3 : ⟦ lim 0 ⟧ (λ h, g (a+h)) = 0).
  {
    apply limit_comp with (b := a); [auto_limit | exact H2 |].
    exists 1. split; [lra |]. intros h H3. solve_R.
  }
  assert (H4 : ⟦ lim 0 ⟧ (λ h, g (a-h)) = 0).
  {
    apply limit_comp with (b := a); [auto_limit | exact H2 |].
    exists 1. split; [lra |]. intros h H4. solve_R.
  }
  unfold schwarz_second_derivative.
  apply limit_eq with (f1 := λ h, g (a+h) + g (a-h) + (⟦ Der ^ 2 a ⟧ f)).
  - exists 1. split; [lra |]. intros h H5.
    unfold g, Taylor_remainder, Taylor_polynomial.
    repeat rewrite sum_f_i_Sn_f; try lia. repeat rewrite sum_f_0_0.
    simpl. field. solve_R.
  - pose proof (limit_plus _ _ 0 0 0 H3 H4) as H5.
    pose proof (limit_plus _ _ 0 (0+0) (⟦ Der ^ 2 a ⟧ f) H5 (limit_const 0 (⟦ Der ^ 2 a ⟧ f))) as H6.
    replace (0+0+(⟦ Der ^ 2 a ⟧ f)) with (⟦ Der ^ 2 a ⟧ f) in H6 by ring. exact H6.
Qed.

Lemma lemma_20_23_b :
  let f := λ x, if Rle_dec 0 x then x^2 else -x^2 in
  schwarz_second_derivative f 0 0 /\ ~ nth_differentiable_at 2 f 0.
Proof.
  set (f := λ x, if Rle_dec 0 x then x^2 else -x^2).
  assert (H1 : f 0 = 0) by (unfold f; destruct (Rle_dec 0 0); simpl; lra).
  assert (H2 : schwarz_second_derivative f 0 0).
  {
    unfold schwarz_second_derivative. apply limit_eq with (f1 := λ _, 0).
    - exists 1. split; [lra |]. intros h H3. rewrite H1.
      unfold f. rewrite Rplus_0_l, Rminus_0_l.
      destruct (Rle_dec 0 h), (Rle_dec 0 (-h)); solve_R.
    - apply limit_const.
  }
  split; auto. intros H3.
  pose proof (lemma_20_23_a f 0 H3) as H4.
  assert (H5 : ⟦ Der ^ 2 0 ⟧ f = 0) by (eapply limit_unique; [exact H4 | exact H2]).
  assert (H6 : ⟦ der 0 ⟧ f = (λ _, 0)).
  {
    intros ε H6. exists ε. split; auto. intros h H7.
    rewrite H1, Rplus_0_l. unfold f.
    destruct (Rle_dec 0 h); solve_R.
  }
  pose proof (derivative_at_imp_derive_at f (λ _, 0) 0 H6) as H7.
  pose proof (theorem_20_1 2 0 f ltac:(lia) H3) as H8.
  destruct (H8 (1/2) ltac:(lra)) as [δ [H9 H10]].
  specialize (H10 (δ/2) ltac:(solve_R)).
  unfold Taylor_polynomial in H10.
  rewrite (sum_f_i_Sn_f _ 0 1) in H10 by lia.
  rewrite (sum_f_i_Sn_f _ 0 0) in H10 by lia. rewrite sum_f_0_0 in H10.
  rewrite nth_derive_at_0, nth_derive_at_1, H1, H5, H7 in H10.
  unfold f in H10. destruct (Rle_dec 0 (δ/2)); solve_R.
Qed.

Lemma lemma_20_23_c : ∀ f a L,
  (∃ δ, δ > 0 /\ ∀ x, |x-a| < δ -> f x <= f a) ->
  schwarz_second_derivative f a L -> L <= 0.
Proof.
  intros f a L [δ [H1 H2]] H3.
  destruct (Rle_dec L 0) as [H4 | H4]; auto.
  destruct (H3 L ltac:(lra)) as [η [H5 H6]].
  set (h := Rmin δ η / 2).
  assert (H7 : 0 < h /\ h < δ /\ h < η) by (unfold h; solve_R).
  specialize (H6 h ltac:(solve_R)).
  pose proof (H2 (a+h) ltac:(solve_R)) as H8.
  pose proof (H2 (a-h) ltac:(solve_R)) as H9.
  assert (H10 : (f (a+h) + f (a-h) - 2*f a) / h^2 <= 0).
  { apply (Rmult_le_reg_r (h^2)); [nra |].
    field_simplify; nra. }
  solve_R.
Qed.

Lemma lemma_20_23_d : ∀ f a,
  nth_differentiable_at 3 f a ->
  ⟦ lim 0 ⟧ (λ h, (f (a+h) - f (a-h) - 2*h*⟦ Der a ⟧ f) / h^3) =
    ⟦ Der ^ 3 a ⟧ f / 3.
Proof.
  intros f a H1.
  pose proof (theorem_20_1 3 a f ltac:(lia) H1) as H2.
  set (g := λ x, R(3,a,f) x / (x-a)^3).
  assert (H3 : ⟦ lim 0 ⟧ (λ h, g (a+h)) = 0).
  {
    apply limit_comp with (b := a); [auto_limit | exact H2 |].
    exists 1. split; [lra |]. intros h H3. solve_R.
  }
  assert (H4 : ⟦ lim 0 ⟧ (λ h, g (a-h)) = 0).
  {
    apply limit_comp with (b := a); [auto_limit | exact H2 |].
    exists 1. split; [lra |]. intros h H4. solve_R.
  }
  apply limit_eq with (f1 := λ h, g (a+h) + g (a-h) + (⟦ Der ^ 3 a ⟧ f / 3)).
  - exists 1. split; [lra |]. intros h H5.
    unfold g, Taylor_remainder, Taylor_polynomial.
    repeat rewrite sum_f_i_Sn_f; try lia. repeat rewrite sum_f_0_0.
    unfold nth_derive_at. simpl. unfold derive. field. solve_R.
  - pose proof (limit_plus _ _ 0 0 0 H3 H4) as H5.
    pose proof (limit_plus _ _ 0 (0+0) (⟦ Der ^ 3 a ⟧ f / 3) H5 (limit_const 0 (⟦ Der ^ 3 a ⟧ f / 3))) as H6.
    replace (0+0+(⟦ Der ^ 3 a ⟧ f / 3)) with (⟦ Der ^ 3 a ⟧ f / 3) in H6 by ring. exact H6.
Qed.
