From Calculus.Chapter5 Require Import Prelude.

Section Problem24.
  Variable A : nat → Ensemble R.

  Hypothesis H1 : ∀ n, Finite_set (A n).
  Hypothesis H2 : ∀ n, (A n) ⊆ [0,1].
  Hypothesis H3 : ∀ m n, m ≠ n → (A m) ⋂ (A n) = ∅.

  Definition f (x : R) : R :=
    match excluded_middle_informative (∃ n, x ∈ A n) with
    | left H4 => 1 / (proj1_sig (constructive_indefinite_description (λ n, x ∈ A n) H4))
    | right _ => 0
    end.

  Lemma f_spec_in : ∀ x n, x ∈ A n → f x = 1 / n.
  Proof.
    intros x n H4. unfold f.
    destruct (excluded_middle_informative (∃ k, x ∈ A k)) as [H5 | H5]; [| exfalso; apply H5; exists n; exact H4].
    destruct (constructive_indefinite_description _ H5) as [m H6]. simpl.
    destruct (Nat.eq_dec m n) as [H7 | H7]; [subst; auto |].
    assert (H8 : x ∈ (A m) ⋂ (A n)) by (constructor; auto).
    rewrite H3 in H8; auto. destruct H8.
  Qed.

  Lemma f_spec_out : ∀ x, (∀ n, x ∉ A n) → f x = 0.
  Proof.
    intros x H4. unfold f.
    destruct (excluded_middle_informative (∃ k, x ∈ A k)) as [H5 | H5]; auto.
    exfalso. destruct H5 as [n H5]. apply (H4 n). exact H5.
  Qed.

  Lemma min_dist_finite : ∀ S a,
    Finite_set S →
    ∃ δ, δ > 0 ∧ ∀ x, x ∈ S → x ≠ a → Rabs (x - a) >= δ.
  Proof.
    clear.
    intros S a [l H1]; subst.
    induction l as [| h t IH].
    - exists 1. split; [lra | intros x H2; inversion H2].
    - destruct IH as [δ [H2 H3]].
      destruct (Req_dec h a) as [H4 | H4].
      + exists δ. split; [exact H2 |].
        intros x H5 H6. simpl in H5. apply In_Union_def in H5 as [H5 | H5].
        * subst. apply In_singleton_def in H5. contradiction.
        * apply H3; assumption.
      + exists (Rmin δ (|(h - a)|)). split; [solve_R |].
        intros x H5 H6. simpl in H5. apply In_Union_def in H5 as [H5 | H5].
          -- apply In_singleton_def in H5. solve_R.
          -- eapply Rge_trans; auto; solve_R.
  Qed.

  Lemma min_dist_nat : ∀ (A : nat → Ensemble R) a (n : nat),
    (∀ k, ∃ δ, δ > 0 ∧ ∀ x, x ∈ A k → x ≠ a → |x - a| ≥ δ) →
    ∃ δ, δ > 0 ∧ ∀ (k : nat) x, (k ≤ n)%nat → x ∈ A k → x ≠ a → |x - a| ≥ δ.
  Proof.
    clear.
    intros B a n H1. induction n as [| n IH].
    - destruct (H1 0%nat) as [δ [H2 H3]].
      exists δ. split; [auto |].
      intros k x H4 H5 H6. 
      assert (H7 : k = 0%nat).
      {
        apply INR_eq. pose proof (pos_INR k) as H7.
        replace 0 with (0%nat : ℝ) in H7 by reflexivity. lra.
      }
      subst. auto.
    - destruct IH as [δ1 [H2 H3]].
      destruct (H1 (S n)) as [δ2 [H4 H5]].
      exists (Rmin δ1 δ2). split; [solve_R |].
      intros k x H6 H7 H8.
      assert ((k ≤ n)%nat ∨ k = S n) as [H9 | H9].
      { apply INR_le in H6. inversion H6; [auto | left; apply le_INR; auto]. }
      + eapply Rge_trans. eapply H3; eauto. solve_R.
      + subst. eapply Rge_trans; [apply H5; eassumption | solve_R].
  Qed.

  Lemma lemma_5_24 : ∀ a, a ∈ [0,1] → ⟦ lim a ⟧ f = 0.
  Proof.
    intros a H4 ε H5.
    destruct (INR_unbounded (1 / ε)) as [n H6].
    assert (H7 : ∀ k, ∃ δ, δ > 0 ∧ ∀ x, x ∈ A k → x ≠ a → |x - a| ≥ δ).
    { intros k. apply min_dist_finite, H1. }
    destruct (min_dist_nat A a n H7) as [δ [H8 H9]].
    exists δ. split; [solve_R |].
    intros x [H10 H11]. 
    rewrite Rminus_0_r.
    destruct (excluded_middle_informative (∃ k, x ∈ A k)) as [[k H12] | H12].
    - rewrite (f_spec_in x k H12).
      assert (H13 : (k > n)%nat).
      {
        destruct (le_dec k n) as [H13 | H13]; [| lia].
        assert (H14 : x ≠ a) by (intros H14; subst; solve_R).
        pose proof (H9 k x ltac:(solve_R) H12 H14) as H15.
        solve_R.
      }
      assert (H14 : 1 / ε < k).
      { eapply Rlt_trans; [exact H6 | apply lt_INR; lia]. }
      assert (H15 : 0 < k). { pose proof Rdiv_pos_pos 1 ε; lra. }
      rewrite Rabs_right; [| pose proof Rdiv_pos_pos 1 k; lra].
      apply Rmult_lt_reg_r with (r := k); auto.
      apply Rmult_lt_compat_r with (r := ε) in H14; auto.
      field_simplify in H14; try lra. field_simplify; lra.
    - assert (H13 : ∀ k, x ∉ A k) by (intros k H13; apply H12; exists k; exact H13).
      rewrite (f_spec_out x H13).
      solve_R.
  Qed.

End Problem24.