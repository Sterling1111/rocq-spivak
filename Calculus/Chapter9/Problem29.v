From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_29 : ∀ n f,
  (0 < n)%nat ->
  (∀ x, x >= 0 -> f x = x^n) ->
  (∀ x, x <= 0 -> f x = 0) ->
  ⟦ der ^ (n - 1) ⟧ f =
    (λ x, if Rle_dec 0 x then (fact n)%nat * x else 0) /\
  ~ nth_differentiable_at n f 0.
Proof.
  assert (H1 : ∀ m g,
    (0 < m)%nat ->
    (∀ x, x >= 0 -> g x = x ^ (S m)) ->
    (∀ x, x <= 0 -> g x = 0) ->
    ⟦ der ⟧ g = (λ x, (S m)%nat * (if Rle_dec 0 x then x ^ m else 0))).
  {
    intros m g H1 H2 H3 x.
    destruct (Rtotal_order x 0) as [H4 | [H4 | H4]].
    - apply derivative_at_eq with (f1 := λ _, 0).
      + exists (-x). split; [lra |]. intros y H5. rewrite H3; solve_R.
      + apply derivative_at_ext_val with (f' := λ _, 0); [auto_diff |].
        destruct (Rle_dec 0 x); lra.
    - subst x. unfold derivative_at.
      rewrite (H3 0 ltac:(lra)).
      destruct (Rle_dec 0 0); [| lra]. rewrite pow_i; [| lia].
      rewrite Rmult_0_r. apply limit_iff. split.
      + apply limit_left_eq with (f1 := λ _, 0); [| auto_limit].
        exists 1. split; [lra |]. intros h H4. rewrite H3; solve_R.
      + apply limit_right_eq with (f1 := λ h, h ^ m).
        * exists 1. split; [lra |]. intros h H4. rewrite H2; [| lra].
          rewrite Rplus_0_l. simpl. field. lra.
        * replace 0 with (0 ^ m) at 2 by (rewrite pow_i; auto; lia). auto_limit.
    - apply derivative_at_eq with (f1 := λ y, y ^ (S m)).
      + exists x. split; [lra |]. intros y H5. rewrite H2; solve_R.
      + apply derivative_at_ext_val with (f' := λ y, (S m)%nat * y ^ (S m - 1)).
        * apply derivative_at_pow.
        * destruct (Rle_dec 0 x); [replace (S m - 1)%nat with m by lia; reflexivity | lra].
  }
  assert (H2 : ∀ n f,
    (0 < n)%nat ->
    (∀ x, x >= 0 -> f x = x ^ n) ->
    (∀ x, x <= 0 -> f x = 0) ->
    ⟦ der ^ (n - 1) ⟧ f = (λ x, if Rle_dec 0 x then (fact n)%nat * x else 0)).
  {
    induction n as [| n IH]; intros f H2 H3 H4; [lia |].
    destruct n as [| n].
    - simpl. extensionality x. destruct (Rle_dec 0 x) as [H5 | H5].
      + rewrite H3; [lra | lra].
      + apply H4. lra.
    - set (g := λ x, if Rle_dec 0 x then x ^ (S n) else 0).
      assert (H5 : ⟦ der ⟧ f = (λ x, (S (S n))%nat * g x)).
      { apply H1; auto; lia. }
      assert (H6 : ⟦ der ^ (S n - 1) ⟧ g = (λ x, if Rle_dec 0 x then (fact (S n))%nat * x else 0)).
      {
        apply IH; [lia | |]; intros x H6; unfold g; destruct (Rle_dec 0 x); try lra.
        assert (x = 0) by lra. subst x. simpl. lra.
      }
      replace (S (S n) - 1)%nat with (S (S n - 1)) by lia.
      apply nth_derivative_succ_iff. exists (λ x, (S (S n))%nat * g x). split; auto.
      replace (λ x, if Rle_dec 0 x then (fact (S (S n)))%nat * x else 0)
        with (λ x, (S (S n))%nat * (if Rle_dec 0 x then (fact (S n))%nat * x else 0)).
      + apply nth_derivative_mult_const_l. exact H6.
      + extensionality x. replace (fact (S (S n))) with (S (S n) * fact (S n))%nat by reflexivity.
        rewrite mult_INR. destruct (Rle_dec 0 x); ring.
  }
  intros n f H3 H4 H5.
  pose proof (H2 n f H3 H4 H5) as H6. split; auto.
  intros H7.
  apply (nth_differentiable_at_imp_differentiable_at_derive_pred n f 0 H3) in H7.
  assert (H8 : (λ x, ⟦ Der ^ (n - 1) x ⟧ f) = (λ x, if Rle_dec 0 x then (fact n)%nat * x else 0)).
  { extensionality x. apply nth_derivative_imp_nth_derive in H6. unfold nth_derive_at. rewrite H6. reflexivity. }
  rewrite H8 in H7. destruct H7 as [L H7].
  destruct (Rle_dec 0 0); [| lra]. rewrite Rmult_0_r in H7.
  apply limit_iff in H7 as [H7 H9].
  assert (H10 : ⟦ lim 0⁻ ⟧ (λ h, ((if Rle_dec 0 (0 + h) then (fact n)%nat * (0 + h) else 0) - 0) / h) = 0).
  {
    apply limit_left_eq with (f1 := λ _, 0); [| auto_limit].
    exists 1. split; [lra |]. intros h H10. destruct (Rle_dec 0 (0 + h)); lra.
  }
  assert (H11 : ⟦ lim 0⁺ ⟧ (λ h, ((if Rle_dec 0 (0 + h) then (fact n)%nat * (0 + h) else 0) - 0) / h) = ((fact n)%nat : ℝ)).
  {
    apply limit_right_eq with (f1 := λ _, ((fact n)%nat : ℝ)); [| auto_limit].
    exists 1. split; [lra |]. intros h H11. destruct (Rle_dec 0 (0 + h)); solve_R.
  }
  pose proof (limit_left_unique _ _ _ _ H10 H7) as H12.
  pose proof (limit_right_unique _ _ _ _ H11 H9) as H13.
  pose proof (INR_fact_lt_0 n). lra.
Qed.
