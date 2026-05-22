From Calculus.Chapter9 Require Import Prelude.

Section section_9_27.

Variable n : ℕ.

Definition S_n x := x^n.

Lemma lemma_9_27 : forall k,
  (0 <= k <= n)%nat -> ⟦ der ^ k ⟧ (S_n) = (fun x => k! * (n ∁ k) * x ^ (n - k)).
Proof.
  intros k H1. induction k as [| k IH].
  - simpl. rewrite n_choose_0. extensionality x. rewrite Nat.sub_0_r. unfold S_n. lra.
  - exists (fun x : R => k! * n ∁ k * x ^ (n - k)).
    split.
    + apply IH; lia.
    + apply derivative_ext with (f1' := fun x => (k! * n ∁ k) * ((n - k) * x ^ (n - k - 1))).
      {
        intros x.
        replace (n - S k)%nat with (n - k - 1)%nat by lia.
        rewrite <- Rmult_assoc. f_equal.
        rewrite fact_simpl.
        unfold choose.
        assert (H2: n <? k = false).
        { apply Nat.ltb_ge. lia. }
        assert (H3: n <? S k = false).
        { apply Nat.ltb_ge. lia. }
        rewrite H2, H3.
        replace (n - k)%nat with (S (n - S k)) by lia.
        repeat rewrite fact_simpl.
        rewrite <- minus_INR; try lia.
        solve_R.
        repeat split; try apply INR_fact_neq_0.
        apply Rmult_integral_contrapositive.
        split. admit. apply INR_fact_neq_0.
        Set Printing Coercions.
        admit.
      }
      auto_diff.
Abort.

End section_9_27.